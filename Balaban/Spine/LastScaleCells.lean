/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LastScaleGeom

/-!
# The last-scale terms read through the cells (A6-3 (d), blocker 7)

The pieces of the two-torus agreement step of the last scale (`Spine/LastScaleAgree.lean`) that
concern one torus at a time or a pair of tori:

* the unit `ℓ¹` balls of the sources of a torus (`torusBall`) and of `ℤ^d` (`zBall`, finitary), the
  extension `extZ` of the sources of a torus to `ℤ^d`, and the space `anW` of the functions of the
  sources on `ℤ^d` that are analytic on the ball of every torus after `extZ`; it is closed under
  bounded uniform limits (`anW_closed`), so the limit over tori of analytic terms is analytic;
* the admissible tori with at least two blocks per side (`TwoCell`) and, on them, the term of a set
  of centred cells (`cellTerm`: the increment of the per-torus family at the fine sites of the cells,
  at the source pulled back by the cell-aligned lift); its locality, analyticity and bound;
* the identification of the increment at the image of a set `A ⊂ ℤ^d` of the cell box with the
  cell term of its cells (`incr_eq_cellTerm`), the margin of `A` in cells (`cellMargin`), and the
  transfer of the polymer property between two tori whose quarter boxes contain `A`
  (`isPolymer_transfer_quarter`, `quarter_cells`).
-/

@[expose] public section

open Finset Filter Topology Balaban Balaban.Polymer Balaban.Polymer.TwoTorusStep

namespace Balaban.RootFSpine.LastScale

variable {d N : ℕ}

/-- The unit `ℓ¹` ball of the sources of a torus. -/
def torusBall (d N ℓ : ℕ) [NeZero ℓ] : Set (Torus d ℓ → Fin N → ℂ) :=
  {g | ∑ y, ∑ i, ‖g y i‖ < 1}

/-- The unit `ℓ¹` ball of the sources on `ℤ^d`, in finitary form: every finite partial sum is
less than one. -/
def zBall (d N : ℕ) : Set ((Fin d → ℤ) → Fin N → ℂ) :=
  {G | ∀ F : Finset (Fin d → ℤ), ∑ y ∈ F, ∑ i, ‖G y i‖ < 1}

theorem isOpen_torusBall (ℓ : ℕ) [NeZero ℓ] : IsOpen (torusBall d N ℓ) := by
  refine isOpen_lt ?_ continuous_const
  refine continuous_finsetSum _ fun y _ => continuous_finsetSum _ fun i _ => ?_
  exact (continuous_apply i |>.comp (continuous_apply y)).norm

variable {s K ℓ : ℕ}

theorem extZ_mem_zBall [NeZero ℓ] {g : Torus d ℓ → Fin N → ℂ} (hg : g ∈ torusBall d N ℓ) :
    extZ s K ℓ g ∈ zBall d N := by
  classical
  intro F
  have hsplit : ∑ y ∈ F, ∑ i, ‖extZ s K ℓ g y i‖ =
      ∑ y ∈ F.filter (fun y => liftZ s K (fun μ => ((y μ : ℤ) : ZMod ℓ)) = y),
        ∑ i, ‖g (fun μ => ((y μ : ℤ) : ZMod ℓ)) i‖ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold extZ
    split_ifs <;> simp
  rw [hsplit]
  have hinj : Set.InjOn (fun y : Fin d → ℤ => (fun μ => ((y μ : ℤ) : ZMod ℓ)))
      (F.filter (fun y => liftZ s K (fun μ => ((y μ : ℤ) : ZMod ℓ)) = y) : Set (Fin d → ℤ)) := by
    intro y hy y' hy' h
    have h1 := (Finset.mem_filter.1 hy).2
    have h2 := (Finset.mem_filter.1 hy').2
    simp only at h
    rw [← h1, ← h2, h]
  rw [← Finset.sum_image (f := fun z => ∑ i, ‖g z i‖) hinj]
  refine lt_of_le_of_lt (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun _ _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hg

theorem pull_mem_torusBall [NeZero ℓ] (hn : ℓ = s * K) {G : (Fin d → ℤ) → Fin N → ℂ}
    (hG : G ∈ zBall d N) : (fun z => G (liftZ s K z)) ∈ torusBall d N ℓ := by
  classical
  show ∑ z, ∑ i, ‖G (liftZ s K z) i‖ < 1
  rw [← Finset.sum_image (f := fun y => ∑ i, ‖G y i‖) (fun z _ z' _ h => liftZ_injective hn h)]
  exact hG _

/-- The linear map `g ↦ (z ↦ extZ g (liftZ z))` from the sources of `ℤ/ℓ₁` to those of `ℤ/ℓ`. -/
noncomputable def pullExt (s K₁ ℓ₁ K ℓ : ℕ) :
    (Torus d ℓ₁ → Fin N → ℂ) →ₗ[ℂ] (Torus d ℓ → Fin N → ℂ) where
  toFun g := fun z => extZ s K₁ ℓ₁ g (liftZ s K z)
  map_add' g g' := by
    funext z i
    simp only [extZ, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c g := by
    funext z i
    simp only [extZ, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

/-- The functions of the sources on `ℤ^d` whose composition with the extension `extZ` of the
sources of every torus is analytic on the unit ball of that torus. -/
def anW (d N s : ℕ) : Submodule ℂ (((Fin d → ℤ) → Fin N → ℂ) → ℂ) where
  carrier := {f | ∀ (ℓ : ℕ) [NeZero ℓ],
    AnalyticOnNhd ℂ (fun g => f (extZ s (ℓ / s) ℓ g)) (torusBall d N ℓ)}
  add_mem' {f f'} hf hf' ℓ _ := (hf ℓ).add (hf' ℓ)
  zero_mem' ℓ _ := analyticOnNhd_const
  smul_mem' c f hf ℓ _ := by
    have h := (analyticOnNhd_const (v := c) (s := torusBall d N ℓ)).smul (hf ℓ)
    exact h

theorem mem_anW {f : ((Fin d → ℤ) → Fin N → ℂ) → ℂ} {s : ℕ} :
    f ∈ anW d N s ↔ ∀ (ℓ : ℕ) [NeZero ℓ],
      AnalyticOnNhd ℂ (fun g => f (extZ s (ℓ / s) ℓ g)) (torusBall d N ℓ) := Iff.rfl

/-- `anW` is closed under bounded uniform limits on the ball `zBall`. -/
theorem anW_closed (f : ℕ → ((Fin d → ℤ) → Fin N → ℂ) → ℂ) (F : ((Fin d → ℤ) → Fin N → ℂ) → ℂ)
    (Mb : ℝ) (hf : ∀ᶠ n in atTop, f n ∈ anW d N s)
    (hM : ∀ᶠ n in atTop, ∀ G ∈ zBall d N, ‖f n G‖ ≤ Mb)
    (hu : TendstoUniformlyOn f F atTop (zBall d N)) : F ∈ anW d N s := by
  refine mem_anW.2 fun ℓ _ => ?_
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 (hf.and hM)
  have hu' : TendstoUniformlyOn (fun n => f n ∘ extZ s (ℓ / s) ℓ) (F ∘ extZ s (ℓ / s) ℓ) atTop
      (torusBall d N ℓ) :=
    (hu.comp (extZ s (ℓ / s) ℓ)).mono fun g hg => extZ_mem_zBall hg
  refine Balaban.Analysis.analyticOnNhd_of_tendstoUniformlyOn
    (f := fun k => fun g => f (k + n0) (extZ s (ℓ / s) ℓ g)) (isOpen_torusBall ℓ)
    (fun k => mem_anW.1 (hn0 (k + n0) (by omega)).1 ℓ) (M := Mb)
    (fun k g hg => (hn0 (k + n0) (by omega)).2 _ (extZ_mem_zBall hg)) ?_
  rw [Metric.tendstoUniformlyOn_iff] at hu' ⊢
  intro ε hε
  exact (tendsto_add_atTop_nat n0).eventually (hu' ε hε)

/-- The admissible tori (`s' ∣ ℓ`) with at least two blocks of side `s` per side. -/
abbrev TwoCell (s s' : ℕ) := {ℓ : ℕ // s' ∣ ℓ ∧ 0 < s ∧ s ∣ ℓ ∧ 2 * s ≤ ℓ}

namespace TwoCell

variable {s s' : ℕ} (i : TwoCell s s')

theorem pos : 0 < i.1 := by have := i.2; omega

instance : NeZero i.1 := ⟨i.pos.ne'⟩

theorem eq : i.1 = s * (i.1 / s) := (Nat.mul_div_cancel' i.2.2.2.1).symm

theorem two_le : 2 ≤ i.1 / s :=
  (Nat.le_div_iff_mul_le i.2.2.1).2 (by have := i.2.2.2.2; linarith)

instance neZeroK : NeZero (i.1 / s) := ⟨by have := i.two_le; omega⟩

end TwoCell

/-- The last-scale term of a set of centred cells on a torus of `TwoCell`, read through the cells:
the increment of `aT` at the fine sites of the cells, at the source pulled back by the lift. -/
noncomputable def cellTerm (s s' : ℕ)
    (aT : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ)
    (i : TwoCell s s') (G : (Fin d → ℤ) → Fin N → ℂ) (X : Finset (Fin d → ℤ)) : ℂ :=
  aT i.1 (sitesT s (i.1 / s) i.1 X) (fun z => G (liftZ s (i.1 / s) z)) -
    aT i.1 (sitesT s (i.1 / s) i.1 X) 0

/-- The margin of a finite set `A ⊂ ℤ^d` in the cell box `|c_μ| ≤ K/4` of blocks of side `s`: the
number of cells between its farthest cell and the edge of the box. -/
def cellMargin (s K : ℕ) (A : Finset (Fin d → ℤ)) : ℕ :=
  K / 4 - A.sup fun y => Finset.univ.sup fun μ => (y μ / (s : ℤ)).natAbs

section Lift

variable {s K ℓ : ℕ}

theorem mem_image_liftZ_sitesT [NeZero ℓ] [NeZero K] (hn : ℓ = s * K) (hs : 0 < s)
    {X : Finset (Fin d → ℤ)} (hX : X ∈ cellPolys d K) (y : Fin d → ℤ) :
    y ∈ (sitesT s K ℓ X).image (liftZ s K) ↔ (fun μ => y μ / (s : ℤ)) ∈ X := by
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    convert mem_sitesT.1 hz using 1
    funext μ
    exact liftZ_ediv hs z μ
  · intro hy
    obtain ⟨Y, -, rfl⟩ := mem_cellPolys.1 hX
    have hvma : ∀ μ, ((y μ / (s : ℤ) : ℤ) : ZMod K).valMinAbs = y μ / (s : ℤ) := by
      obtain ⟨b, -, he⟩ := Finset.mem_image.1 hy
      intro μ
      have h1 := congrFun he μ
      rw [← h1, ZMod.coe_valMinAbs]
    have hl := liftZ_cast hn hs (Nat.pos_of_ne_zero (NeZero.ne K)) y hvma
    refine Finset.mem_image.2 ⟨_, ?_, hl⟩
    rw [mem_sitesT]
    convert hy using 1
    funext μ
    rw [← liftZ_ediv hs _ μ, hl]

theorem image_cast_of_mem_iff [NeZero ℓ] [NeZero K] (hn : ℓ = s * K) (hs : 0 < s)
    {X : Finset (Fin d → ℤ)} (hX : X ∈ cellPolys d K) {A : Finset (Fin d → ℤ)}
    (hA : ∀ y, y ∈ A ↔ (fun μ => y μ / (s : ℤ)) ∈ X) :
    A.image (fun y μ => ((y μ : ℤ) : ZMod ℓ)) = sitesT s K ℓ X := by
  have hA' : A = (sitesT s K ℓ X).image (liftZ s K) := by
    ext y; rw [hA, mem_image_liftZ_sitesT hn hs hX]
  rw [hA', Finset.image_image]
  have : ((fun (y : Fin d → ℤ) μ => ((y μ : ℤ) : ZMod ℓ)) ∘ liftZ (ℓ := ℓ) s K) = id := by
    funext z; exact cast_liftZ hn z
  rw [this, Finset.image_id]

theorem card_of_mem_iff [NeZero ℓ] [NeZero K] (hn : ℓ = s * K) (hs : 0 < s)
    {X : Finset (Fin d → ℤ)} (hX : X ∈ cellPolys d K) {A : Finset (Fin d → ℤ)}
    (hA : ∀ y, y ∈ A ↔ (fun μ => y μ / (s : ℤ)) ∈ X) :
    A.card = s ^ d * X.card := by
  have hA' : A = (sitesT s K ℓ X).image (liftZ s K) := by
    ext y; rw [hA, mem_image_liftZ_sitesT hn hs hX]
  rw [hA', Finset.card_image_of_injective _ (liftZ_injective hn)]
  obtain ⟨Y, -, rfl⟩ := mem_cellPolys.1 hX
  exact card_sitesT hn Y

theorem image_ediv_of_mem_iff [NeZero ℓ] [NeZero K] (hn : ℓ = s * K) (hs : 0 < s)
    {X : Finset (Fin d → ℤ)} (hX : X ∈ cellPolys d K) {A : Finset (Fin d → ℤ)}
    (hA : ∀ y, y ∈ A ↔ (fun μ => y μ / (s : ℤ)) ∈ X) :
    A.image (fun y μ => y μ / (s : ℤ)) = X := by
  have hA' : A = (sitesT s K ℓ X).image (liftZ s K) := by
    ext y; rw [hA, mem_image_liftZ_sitesT hn hs hX]
  rw [hA', Finset.image_image]
  have : ((fun (y : Fin d → ℤ) μ => y μ / (s : ℤ)) ∘ liftZ (ℓ := ℓ) s K) =
      cellZ (ℓ := ℓ) s K := by
    funext z μ; exact liftZ_ediv hs z μ
  rw [this]
  obtain ⟨Y, -, rfl⟩ := mem_cellPolys.1 hX
  exact image_cellZ_sitesT hn hs Y

theorem cellMargin_of_mem_iff [NeZero ℓ] [NeZero K] (hn : ℓ = s * K) (hs : 0 < s)
    {X : Finset (Fin d → ℤ)} (hX : X ∈ cellPolys d K) {A : Finset (Fin d → ℤ)}
    (hA : ∀ y, y ∈ A ↔ (fun μ => y μ / (s : ℤ)) ∈ X) :
    cellMargin s K A = K / 4 - X.sup fun x => Finset.univ.sup fun μ => (x μ).natAbs := by
  unfold cellMargin
  congr 1
  rw [← image_ediv_of_mem_iff hn hs hX hA, Finset.sup_image]
  rfl

/-- On the cells of the box `|c_μ| ≤ K/4` the centred representative of a fine site is its lift. -/
theorem valMinAbs_eq_liftZ [NeZero ℓ] (hn : ℓ = s * K) (hs : 0 < s) (hK : 2 ≤ K)
    {z : Torus d ℓ} (hz : ∀ μ, (cellZ s K z μ).natAbs ≤ K / 4) :
    (fun μ => (z μ).valMinAbs) = liftZ s K z := by
  funext μ
  have h2 : 2 * |liftZ s K z μ| < (s : ℤ) * K :=
    two_abs_lt_of_cell hs hK (by rw [liftZ_ediv hs z μ]; exact hz μ)
  have h3 : ((liftZ s K z μ : ℤ) : ZMod ℓ) = z μ := congrFun (cast_liftZ hn z) μ
  rw [← h3]
  have hℓ : ((ℓ : ℕ) : ℤ) = (s : ℤ) * K := by rw [hn]; push_cast; ring
  exact valMinAbs_cast_of_two_abs_lt (by rw [hℓ]; exact h2)

end Lift

section Quarter

variable {s : ℕ}

/-- **The polymer property of a quarter-box set on two tori.** If the image of a finite set `A` of
the quarter box of `ℤ/ℓ` is a polymer of blocks of side `s ≥ 4`, then `ℓ` has at least four blocks
per side, `A` is closed under the blocks of `ℤ^d`, and for every torus `ℤ/ℓ'` (`s ∣ ℓ'`) whose
quarter box contains `A`, `ℓ'` has at least four blocks per side and the image of `A` is a
polymer. -/
theorem isPolymer_transfer_quarter (hd : 0 < d) (hs4 : 4 ≤ s) {ℓ ℓ' : ℕ} [NeZero ℓ] [NeZero ℓ']
    (hsℓ : s ∣ ℓ) (hsℓ' : s ∣ ℓ') {A : Finset (Fin d → ℤ)}
    (hA : ∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ)) (hA' : ∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ' : ℤ))
    (hP : IsPolymer d ℓ s (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ))) :
    4 ≤ ℓ / s ∧ 4 ≤ ℓ' / s ∧ IsPolymer d ℓ' s (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ')) ∧
      (∀ y ∈ A, ∀ y' : Fin d → ℤ, (∀ μ, y μ / (s : ℤ) = y' μ / (s : ℤ)) → y' ∈ A) := by
  have hn : ℓ = s * (ℓ / s) := (Nat.mul_div_cancel' hsℓ).symm
  have hn' : ℓ' = s * (ℓ' / s) := (Nat.mul_div_cancel' hsℓ').symm
  have hK4 := four_le_of_isPolymer_quarter hd hn hs4 A hA hP
  obtain ⟨hne, hcl, -⟩ := isPolymer_fwd_quarter hn hK4 A hA hP
  obtain ⟨y0, hy0⟩ := hne
  have hA's : ∀ y ∈ A, ∀ μ, 4 * |y μ| < (s : ℤ) * ((ℓ' / s : ℕ) : ℤ) := fun y hy μ => by
    have h := hA' y hy μ
    have : ((ℓ' : ℕ) : ℤ) = (s : ℤ) * ((ℓ' / s : ℕ) : ℤ) := by
      conv_lhs => rw [hn']
      push_cast; ring
    rwa [this] at h
  have hK4' := (quarter_of_blockClosed hs4 hcl hA's hy0 ⟨0, hd⟩).1
  exact ⟨hK4, hK4', (isPolymer_image_cast_iff_of_quarter hn hn' hK4 hK4' A hA hA').1 hP, hcl⟩

/-- The cells of a block-closed quarter-box set whose image is a polymer: they form the centred
image of an animal of the block torus, lie in the cell box `|c_μ| ≤ K/4`, and determine the set. -/
theorem quarter_cells (hs4 : 4 ≤ s) {ℓ K : ℕ} [NeZero ℓ] [NeZero K] (hn : ℓ = s * K) (hK2 : 2 ≤ K)
    {A : Finset (Fin d → ℤ)} (hA : ∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ))
    (hcl : ∀ y ∈ A, ∀ y' : Fin d → ℤ, (∀ μ, y μ / (s : ℤ) = y' μ / (s : ℤ)) → y' ∈ A)
    (hP : IsPolymer d ℓ s (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ))) :
    A.image (fun y μ => y μ / (s : ℤ)) ∈ cellPolys d K ∧
      (∀ x ∈ A.image (fun y μ => y μ / (s : ℤ)), ∀ μ, (x μ).natAbs ≤ K / 4) ∧
      (∀ y, y ∈ A ↔ (fun μ => y μ / (s : ℤ)) ∈ A.image (fun y μ => y μ / (s : ℤ))) := by
  have hs0 : 0 < s := by omega
  have hAs : ∀ y ∈ A, ∀ μ, 4 * |y μ| < (s : ℤ) * K := fun y hy μ => by
    have h := hA y hy μ
    have : ((ℓ : ℕ) : ℤ) = (s : ℤ) * K := by rw [hn]; push_cast; ring
    rwa [this] at h
  have hq : ∀ y ∈ A, ∀ μ, (y μ / (s : ℤ)).natAbs ≤ K / 4 := fun y hy μ =>
    (quarter_of_blockClosed hs4 hcl hAs hy μ).2
  have hQ : ∀ x ∈ A.image (fun y μ => y μ / (s : ℤ)), ∀ μ, (x μ).natAbs ≤ K / 4 := by
    intro x hx μ
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact hq y hy μ
  refine ⟨?_, hQ, fun y => ⟨fun hy => Finset.mem_image_of_mem _ hy, fun hy => ?_⟩⟩
  · obtain ⟨X₀, hX₀, he⟩ := (isPolymer_iff_sitesT hn hs0 _).1 hP
    obtain ⟨Y, hY, rfl⟩ := mem_cellPolys.1 hX₀
    have h1 := image_cellZ_sitesT (ℓ := ℓ) hn hs0 Y
    rw [he, Finset.image_image] at h1
    have h2 : (cellZ s K ∘ fun (y : Fin d → ℤ) μ => ((y μ : ℤ) : ZMod ℓ)) =ᶠ[Filter.principal A]
        fun y μ => y μ / (s : ℤ) := by
      rw [Filter.EventuallyEq, Filter.eventually_principal]
      intro y hy
      exact cellZ_cast hn hs0 hK2 y (hq y hy)
    rw [Finset.image_congr (fun y hy => h2 hy)] at h1
    rw [h1]
    exact mem_cellPolys.2 ⟨Y, hY, rfl⟩
  · obtain ⟨y', hy', he⟩ := Finset.mem_image.1 hy
    exact hcl y' hy' y fun μ => congrFun he μ

end Quarter

section CellTerm

variable {s s' : ℕ} {aT : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ}

theorem cellTerm_extZ (i : TwoCell s s') (g : Torus d i.1 → Fin N → ℂ) (X : Finset (Fin d → ℤ)) :
    cellTerm s s' aT i (extZ s (i.1 / s) i.1 g) X =
      aT i.1 (sitesT s (i.1 / s) i.1 X) g - aT i.1 (sitesT s (i.1 / s) i.1 X) 0 := by
  unfold cellTerm
  congr 2
  funext z
  exact extZ_liftZ i.eq g z

theorem cellTerm_zero (i : TwoCell s s') (X : Finset (Fin d → ℤ)) :
    cellTerm s s' aT i 0 X = 0 := by
  unfold cellTerm
  have : (fun z : Torus d i.1 => (0 : (Fin d → ℤ) → Fin N → ℂ) (liftZ s (i.1 / s) z)) = 0 := rfl
  rw [this, sub_self]

theorem cellTerm_local
    (hL : ∀ (ℓ : ℕ) [NeZero ℓ], s' ∣ ℓ → ∀ X (g g' : Torus d ℓ → Fin N → ℂ),
      (∀ y ∈ X, g y = g' y) → aT ℓ X g = aT ℓ X g')
    (i : TwoCell s s') (X : Finset (Fin d → ℤ)) (G G' : (Fin d → ℤ) → Fin N → ℂ)
    (h : ∀ y : Fin d → ℤ, (fun μ => y μ / (s : ℤ)) ∈ X → G y = G' y) :
    cellTerm s s' aT i G X = cellTerm s s' aT i G' X := by
  unfold cellTerm
  rw [hL i.1 i.2.1 _ _ _ fun z hz => h _ ?_]
  have hz' := mem_sitesT.1 hz
  convert hz' using 1
  funext μ
  exact liftZ_ediv i.2.2.1 z μ

theorem cellTerm_mem_anW
    (hA : ∀ (ℓ : ℕ) [NeZero ℓ], s' ∣ ℓ → ∀ X, AnalyticOnNhd ℂ (aT ℓ X) (torusBall d N ℓ))
    (i : TwoCell s s') (X : Finset (Fin d → ℤ)) :
    (fun G => cellTerm s s' aT i G X) ∈ anW d N s := by
  refine mem_anW.2 fun ℓ _ => ?_
  have hLan : AnalyticOnNhd ℂ (fun g : Torus d ℓ → Fin N → ℂ =>
      fun z : Torus d i.1 => extZ s (ℓ / s) ℓ g (liftZ s (i.1 / s) z)) (torusBall d N ℓ) := by
    have h := ((pullExt (d := d) (N := N) s (ℓ / s) ℓ (i.1 / s) i.1).toContinuousLinearMap
      ).analyticOnNhd (torusBall d N ℓ)
    rwa [LinearMap.coe_toContinuousLinearMap'] at h
  have hmaps : Set.MapsTo (fun g : Torus d ℓ → Fin N → ℂ =>
      fun z : Torus d i.1 => extZ s (ℓ / s) ℓ g (liftZ s (i.1 / s) z)) (torusBall d N ℓ)
      (torusBall d N i.1) := fun g hg =>
    pull_mem_torusBall i.eq (extZ_mem_zBall hg)
  have h1 := (hA i.1 i.2.1 (sitesT s (i.1 / s) i.1 X)).comp hLan hmaps
  exact h1.sub analyticOnNhd_const

theorem cellTerm_bound {κ' B : ℝ}
    (hBd : ∀ (ℓ : ℕ) [NeZero ℓ], s' ∣ ℓ → ∀ X, ∀ g ∈ torusBall d N ℓ,
      ‖aT ℓ X g - aT ℓ X 0‖ ≤ B * Real.exp (-κ' * ((X.card : ℝ) / (s : ℝ) ^ d)))
    (i : TwoCell s s') {X : Finset (Fin d → ℤ)} (hX : X ∈ cellPolys d (i.1 / s))
    {G : (Fin d → ℤ) → Fin N → ℂ} (hG : G ∈ zBall d N) :
    ‖cellTerm s s' aT i G X‖ ≤ B * Real.exp (-κ' * (X.card : ℝ)) := by
  have h := hBd i.1 i.2.1 (sitesT s (i.1 / s) i.1 X) _ (pull_mem_torusBall i.eq hG)
  have hcard : ((sitesT s (i.1 / s) i.1 X).card : ℝ) / (s : ℝ) ^ d = X.card := by
    obtain ⟨Y, -, rfl⟩ := mem_cellPolys.1 hX
    rw [card_sitesT i.eq Y]
    have hs : (0 : ℝ) < (s : ℝ) ^ d := by
      have := i.2.2.1; positivity
    push_cast
    field_simp
  rw [hcard] at h
  exact h

/-- The increment at the image of a set `A ⊂ ℤ^d` of fine sites whose cells form `X ∈ P` (in the
cell box) is the cell term of `X`. -/
theorem incr_eq_cellTerm
    (hL : ∀ (ℓ : ℕ) [NeZero ℓ], s' ∣ ℓ → ∀ X (g g' : Torus d ℓ → Fin N → ℂ),
      (∀ y ∈ X, g y = g' y) → aT ℓ X g = aT ℓ X g')
    (j : TwoCell s s') {X : Finset (Fin d → ℤ)} (hX : X ∈ cellPolys d (j.1 / s))
    (hQ : ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ j.1 / s / 4) {A : Finset (Fin d → ℤ)}
    (hA : ∀ y, y ∈ A ↔ (fun μ => y μ / (s : ℤ)) ∈ X) (G : (Fin d → ℤ) → Fin N → ℂ) :
    aT j.1 (A.image fun y μ => ((y μ : ℤ) : ZMod j.1)) (fun z => G fun μ => (z μ).valMinAbs) -
        aT j.1 (A.image fun y μ => ((y μ : ℤ) : ZMod j.1)) 0 =
      cellTerm s s' aT j G X := by
  rw [image_cast_of_mem_iff j.eq j.2.2.1 hX hA]
  unfold cellTerm
  congr 1
  refine hL j.1 j.2.1 _ _ _ fun z hz => ?_
  rw [valMinAbs_eq_liftZ j.eq j.2.2.1 j.two_le fun μ => hQ _ (mem_sitesT.1 hz) μ]

end CellTerm

theorem card_sitesT_div {s K ℓ : ℕ} [NeZero ℓ] [NeZero K] (hn : ℓ = s * K) (hs : 0 < s)
    {X : Finset (Fin d → ℤ)} (hX : X ∈ cellPolys d K) :
    ((sitesT s K ℓ X).card : ℝ) / (s : ℝ) ^ d = X.card := by
  obtain ⟨Y, -, rfl⟩ := mem_cellPolys.1 hX
  rw [card_sitesT hn Y]
  have : (0 : ℝ) < (s : ℝ) ^ d := by positivity
  push_cast
  field_simp

end Balaban.RootFSpine.LastScale
