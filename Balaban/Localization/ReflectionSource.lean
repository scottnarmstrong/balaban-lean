/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.ReflectionGreen
public import Balaban.Multiscale.HolderGlobal
public import Balaban.Multiscale.KernelAlgebra
import Mathlib.Tactic.Linarith

/-!
# Source copies on the doubled torus (NC3, Lemma R4, second half)

* `Balaban.Reflection.unfoldPt`: the preimage of a cube point in the chamber `[0, S)^d`;
  `foldTo_unfoldPt`, `foldTo_unfoldPt_add_single`, `foldTo_unfoldPt_sub_single`: it folds back to
  the point, and the fold of its neighbours is the neighbours of the point when these stay in the
  cube (the bond is retained);
* `Balaban.Reflection.card_fibre_le`: a cube point has at most `2^d` preimages;
* `Balaban.Reflection.sourceBlocks`: the (at most `2^d`) reflected `j`-blocks over the block of a
  point `y'`, each containing exactly one preimage of `y'`.
-/

@[expose] public section

namespace Balaban.Reflection

open Matrix Balaban Balaban.Multiscale Balaban.Localization

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {q s : ℕ} {c : Fin d → ℕ} [NeZero s]

/-- The preimage of a cube point `x` in the chamber `[0, S)^d` of the doubled torus. -/
def unfoldPt (N₀ L k q s : ℕ) (c : Fin d → ℕ) (x : Torus d (N₀ * L ^ k)) :
    Torus d (2 * s * L ^ q) :=
  fun i => ((((x i - (c i : ZMod (N₀ * L ^ k))).val : ℕ) : ZMod (2 * s * L ^ q)))

omit [NeZero s] in
theorem loc_spec (h : FoldSetting G q s c) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ cubeOf N₀ L k q s c) (i : Fin d) :
    (x i - (c i : ZMod (N₀ * L ^ k))).val < s * L ^ q ∧
      x i = ((c i + (x i - (c i : ZMod (N₀ * L ^ k))).val : ℕ) : ZMod (N₀ * L ^ k)) := by
  obtain ⟨t, ht, hxt⟩ := mem_cubeSet.1 hx i
  have e : x i - (c i : ZMod (N₀ * L ^ k)) = ((t : ℕ) : ZMod (N₀ * L ^ k)) := by
    rw [hxt]; push_cast; ring
  have hv : (x i - (c i : ZMod (N₀ * L ^ k))).val = t := by
    rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans ht h.side)]
  refine ⟨hv ▸ ht, ?_⟩
  rw [hv, hxt]

omit [NeZero s] in
theorem unfoldPt_val (h : FoldSetting G q s c) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ cubeOf N₀ L k q s c) (i : Fin d) :
    (unfoldPt N₀ L k q s c x i).val = (x i - (c i : ZMod (N₀ * L ^ k))).val := by
  have hlt := (loc_spec h hx i).1
  unfold unfoldPt
  have hlt' : (x i - (c i : ZMod (N₀ * L ^ k))).val < 2 * s * L ^ q := by
    have := L_pow_pos L q
    nlinarith
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt']

theorem foldTo_unfoldPt (h : FoldSetting G q s c) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ cubeOf N₀ L k q s c) : foldTo N₀ L k q s c (unfoldPt N₀ L k q s c x) = x := by
  funext i
  have hv := unfoldPt_val h hx i
  obtain ⟨hlt, hxi⟩ := loc_spec h hx i
  show fold1 (N₀ * L ^ k) (s * L ^ q) (c i) (2 * s * L ^ q) _ = x i
  rw [fold1_eq, hv]
  simp only [foldNat, hlt, ↓reduceIte]
  exact hxi.symm

theorem foldTo_unfoldPt_add_single (h : FoldSetting G q s c) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ cubeOf N₀ L k q s c) (μ : Fin d)
    (hxe : x + Pi.single μ 1 ∈ cubeOf N₀ L k q s c) :
    foldTo N₀ L k q s c (unfoldPt N₀ L k q s c x + Pi.single μ 1) = x + Pi.single μ 1 := by
  have hS : 0 < s * L ^ q := Nat.mul_pos h.s_pos (L_pow_pos L q)
  obtain ⟨h1, -⟩ := foldMap_nbr_low (c := c) (ℓ := N₀ * L ^ k) (two_mul_side L q s) hS h.side
    (unfoldPt N₀ L k q s c x) μ (by rw [unfoldPt_val h hx]; exact (loc_spec h hx μ).1)
  have h2 : foldMap (N₀ * L ^ k) (s * L ^ q) (2 * s * L ^ q) c (unfoldPt N₀ L k q s c x) = x :=
    foldTo_unfoldPt h hx
  change foldMap _ _ _ c _ = _
  rw [h1, h2]
  have hxe' : x + Pi.single μ 1 ∈ cubeSet (N₀ * L ^ k) (s * L ^ q) c := hxe
  unfold stepUpT
  simp only [hxe', ↓reduceIte]

theorem foldTo_unfoldPt_sub_single (h : FoldSetting G q s c) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ cubeOf N₀ L k q s c) (μ : Fin d)
    (hxe : x - Pi.single μ 1 ∈ cubeOf N₀ L k q s c) :
    foldTo N₀ L k q s c (unfoldPt N₀ L k q s c x - Pi.single μ 1) = x - Pi.single μ 1 := by
  have hS : 0 < s * L ^ q := Nat.mul_pos h.s_pos (L_pow_pos L q)
  obtain ⟨-, h1⟩ := foldMap_nbr_low (c := c) (ℓ := N₀ * L ^ k) (two_mul_side L q s) hS h.side
    (unfoldPt N₀ L k q s c x) μ (by rw [unfoldPt_val h hx]; exact (loc_spec h hx μ).1)
  have h2 : foldMap (N₀ * L ^ k) (s * L ^ q) (2 * s * L ^ q) c (unfoldPt N₀ L k q s c x) = x :=
    foldTo_unfoldPt h hx
  change foldMap _ _ _ c _ = _
  rw [h1, h2]
  have hxe' : x - Pi.single μ 1 ∈ cubeSet (N₀ * L ^ k) (s * L ^ q) c := hxe
  unfold stepDnT
  simp only [hxe', ↓reduceIte]

/-- A point has at most `2^d` preimages under the fold. -/
theorem card_fibre_le (h : FoldSetting G q s c) (y : Torus d (N₀ * L ^ k)) :
    (Finset.univ.filter (fun p : Torus d (2 * s * L ^ q) => foldTo N₀ L k q s c p = y)).card ≤
      2 ^ d := by
  classical
  have hS : 0 < s * L ^ q := Nat.mul_pos h.s_pos (L_pow_pos L q)
  by_cases hne : (Finset.univ.filter (fun p : Torus d (2 * s * L ^ q) =>
      foldTo N₀ L k q s c p = y)).Nonempty
  · obtain ⟨p₀, hp₀⟩ := hne
    have hp₀' : foldTo N₀ L k q s c p₀ = y := (Finset.mem_filter.1 hp₀).2
    have hsub : (Finset.univ.filter (fun p : Torus d (2 * s * L ^ q) =>
        foldTo N₀ L k q s c p = y)) ⊆
        Fintype.piFinset (fun i => ({p₀ i, -1 - p₀ i} : Finset (ZMod (2 * s * L ^ q)))) := by
      intro p hp
      have hp' : foldTo N₀ L k q s c p = y := (Finset.mem_filter.1 hp).2
      rw [Fintype.mem_piFinset]
      intro i
      have hi : fold1 (N₀ * L ^ k) (s * L ^ q) (c i) (2 * s * L ^ q) (p₀ i) =
          fold1 (N₀ * L ^ k) (s * L ^ q) (c i) (2 * s * L ^ q) (p i) :=
        (congrFun hp₀' i).trans (congrFun hp' i).symm
      rcases fold1_fibre (two_mul_side L q s) h.side hi with h1 | h1
      · simp [h1]
      · simp [h1]
    refine (Finset.card_le_card hsub).trans ?_
    rw [Fintype.card_piFinset]
    calc ∏ i : Fin d, ({p₀ i, -1 - p₀ i} : Finset (ZMod (2 * s * L ^ q))).card
        ≤ 2 ^ (Finset.univ : Finset (Fin d)).card :=
          Finset.prod_le_pow_card _ _ _ fun i _ => Finset.card_le_two
      _ = 2 ^ d := by simp
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne]
    simp

end Balaban.Reflection

namespace Balaban.Reflection

open Matrix Balaban Balaban.Multiscale Balaban.Localization

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {q s : ℕ} {c : Fin d → ℕ} [NeZero s]

/-- The reflected `j`-blocks over the block of `y'`: the blocks of the doubled torus that contain a
preimage of `y'`. -/
noncomputable def sourceBlocks (N₀ L k q s : ℕ) [NeZero N₀] [NeZero L] [NeZero s] (c : Fin d → ℕ)
    (j : ℕ) (y' : Torus d (N₀ * L ^ k)) : Finset (Torus d (2 * s * L ^ (q - j))) := by
  classical
  exact (Finset.univ.filter (fun p : Torus d (2 * s * L ^ q) => foldTo N₀ L k q s c p = y')).image
    (jBlock d L (2 * s) q j)

theorem card_sourceBlocks_le (h : FoldSetting G q s c) (j : ℕ) (y' : Torus d (N₀ * L ^ k)) :
    (sourceBlocks N₀ L k q s c j y').card ≤ 2 ^ d := by
  classical
  unfold sourceBlocks
  exact Finset.card_image_le.trans (card_fibre_le h y')

/-- A reflected block lies over the block of `y'` iff it is one of the source blocks. -/
theorem jBlock_mem_sourceBlocks_iff (h : FoldSetting G q s c) {j : ℕ} (hjq : j ≤ q)
    (y' : Torus d (N₀ * L ^ k)) (p : Torus d (2 * s * L ^ q)) :
    jBlock d L (2 * s) q j p ∈ sourceBlocks N₀ L k q s c j y' ↔
      jBlock d L N₀ k j (foldTo N₀ L k q s c p) = jBlock d L N₀ k j y' := by
  classical
  unfold sourceBlocks
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p'', hp'', hb⟩
    have h1 : foldTo N₀ L k q s c p'' = y' := (Finset.mem_filter.1 hp'').2
    have := foldTo_jBlock_eq h hjq hb
    rw [h1] at this
    exact this.symm
  · intro hb
    obtain ⟨himg, -⟩ := image_fold_block h hjq p
    have hy : y' ∈ Finset.univ.filter (fun x' : Torus d (N₀ * L ^ k) =>
        jBlock d L N₀ k j x' = jBlock d L N₀ k j (foldTo N₀ L k q s c p)) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hb.symm⟩
    rw [← himg] at hy
    obtain ⟨p'', hp'', hF⟩ := Finset.mem_image.1 hy
    exact ⟨p'', Finset.mem_filter.2 ⟨Finset.mem_univ _, hF⟩,
      (Finset.mem_filter.1 hp'').2⟩

theorem exists_source_pre {j : ℕ}
    (y' : Torus d (N₀ * L ^ k)) {β : Torus d (2 * s * L ^ (q - j))}
    (hβ : β ∈ sourceBlocks N₀ L k q s c j y') :
    ∃ r : Torus d (2 * s * L ^ q), foldTo N₀ L k q s c r = y' ∧ jBlock d L (2 * s) q j r = β := by
  classical
  unfold sourceBlocks at hβ
  obtain ⟨r, hr, hrβ⟩ := Finset.mem_image.1 hβ
  exact ⟨r, (Finset.mem_filter.1 hr).2, hrβ⟩

/-- **The setting of one reflected source.** A source `g` on the doubled torus supported in one
`j'`-block, the block of a preimage `r` of a point of the layer `j'`. -/
noncomputable def reflSetting (h : FoldSetting G q s c) (hd : 3 ≤ d) (hL : 3 ≤ L) {a : ℕ → ℝ}
    {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) (ha : IsAdmissibleWeights k a)
    (α : G.Ω 1 → ℂ) (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))
    {j' : ℕ} (hj'1 : 1 ≤ j') (hj'q : j' ≤ q) (r : Torus d (2 * s * L ^ q))
    (hr : foldTo N₀ L k q s c r ∈ G.layer j') (g : (reflectedGS G h).Ω 1 → ℂ)
    (hg : ∀ x, g x ≠ 0 → jBlock d L (2 * s) q j' x = jBlock d L (2 * s) q j' r) :
    PtSetting (reflectedGS G h) 1 where
  a := a
  ν := ν
  α := reflAlpha h α
  f := g
  j' := j'
  y' := r
  hd := hd
  hL := hL
  hν0 := hν0
  hν1 := by
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (pow_le_pow_right₀ hL1 h.q_le) 2) hν0) hν1
  ha := isAdmissibleWeights_refl h ha
  hα := reflAlpha_bound h hα
  hϱ := hϱ
  hsep := hsep
  hj'1 := hj'1
  hj'k := hj'q
  hy' := (mem_layer_reflectedGS_iff h hj'q r).2 hr
  hsupp := hg

/-- The value of the solution at a point for the source `g`: the field `ũ*` of the reflected
Dirichlet operator on the doubled torus. -/
noncomputable def reflSol (h : FoldSetting G q s c) (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (g : (reflectedGS G h).Ω 1 → ℂ) : Torus d (2 * s * L ^ q) → ℂ :=
  zeroExt ((reflectedGS G h).Ω 1)
    ((dirichletOperator (reflectedGS G h) a ν (reflAlpha h α))⁻¹ *ᵥ g)

/-- **Pointwise bound for one reflected source** (Proposition 4.8 on the reflected set). -/
theorem single_source_U_le (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ K2 : ℝ, 0 ≤ K2 ∧ ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)
      {q s : ℕ} {c : Fin d → ℕ} [NeZero s] (h : FoldSetting G q s c) {a : ℕ → ℝ} {ν : ℝ},
      0 ≤ ν → ν * ((L : ℝ) ^ k) ^ 2 ≤ 1 → IsAdmissibleWeights k a →
      ∀ (α : G.Ω 1 → ℂ), (∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) →
      1 ≤ ϱ → (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) →
      ∀ {j' : ℕ}, 1 ≤ j' → j' ≤ q → ∀ (r : Torus d (2 * s * L ^ q)),
      foldTo N₀ L k q s c r ∈ G.layer j' → ∀ (g : (reflectedGS G h).Ω 1 → ℂ),
      (∀ x, g x ≠ 0 → jBlock d L (2 * s) q j' x = jBlock d L (2 * s) q j' r) →
      ∀ {Mf : ℝ}, 0 ≤ Mf → (∀ x, ‖g x‖ ≤ Mf) → ∀ (p : Torus d (2 * s * L ^ q)),
      ‖reflSol h a ν α g p‖ + (reflectedGS G h).spacing p *
          ∑ μ : Fin d, ‖reflSol h a ν α g (p + Pi.single μ 1) - reflSol h a ν α g p‖ ≤
        K2 * decay (agmonRate d / 2)
          (G.pathDist (foldTo N₀ L k q s c p) (foldTo N₀ L k q s c r)) *
          ((L : ℝ) ^ (2 * j') * Mf) := by
  obtain ⟨K2, hK2, hU⟩ := U_le_decay hd hL
  refine ⟨K2, hK2, ?_⟩
  intro k N₀ _ ϱ G q s c _ h a ν hν0 hν1 ha α hα hϱ hsep j' hj'1 hj'q r hr g hg Mf hMf0 hMf p
  set S := reflSetting h hd hL hν0 hν1 ha α hα hϱ hsep hj'1 hj'q r hr g hg with hS
  have h1 : S.U p ≤ K2 * decay (agmonRate d / 2) ((reflectedGS G h).pathDist p r) *
      ((L : ℝ) ^ (2 * j') * Mf) :=
    hU (reflectedGS G h) S hMf0 hMf (mem_reflectedGS_Ω_one h p)
  have hd0 : 0 ≤ agmonRate d / 2 := by
    have := agmonRate_pos (show 0 < d by omega)
    positivity
  have h2 := decay_anti_dist hd0 (pathDist_fold_le h p r)
  have hF : 0 ≤ (L : ℝ) ^ (2 * j') * Mf := by positivity
  refine le_trans (le_of_eq rfl) (h1.trans ?_)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hK2) hF

/-- **Hölder bound for one reflected source** (`holder_pair_decay` on the reflected set). -/
theorem single_source_holder_le (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ}
      (G : GeneratingSet d L N₀ k ϱ)
      {q s : ℕ} {c : Fin d → ℕ} [NeZero s] (h : FoldSetting G q s c) {a : ℕ → ℝ} {ν : ℝ},
      0 ≤ ν → ν * ((L : ℝ) ^ k) ^ 2 ≤ 1 → IsAdmissibleWeights k a →
      ∀ (α : G.Ω 1 → ℂ), (∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) →
      1 ≤ ϱ → (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) →
      ∀ {j' : ℕ}, 1 ≤ j' → j' ≤ q → ∀ (r : Torus d (2 * s * L ^ q)),
      foldTo N₀ L k q s c r ∈ G.layer j' → ∀ (g : (reflectedGS G h).Ω 1 → ℂ),
      (∀ x, g x ≠ 0 → jBlock d L (2 * s) q j' x = jBlock d L (2 * s) q j' r) →
      ∀ {Mf : ℝ}, 0 ≤ Mf → (∀ x, ‖g x‖ ≤ Mf) → ∀ {p p' : Torus d (2 * s * L ^ q)},
      (reflectedGS G h).layerIndex p ≤ (reflectedGS G h).layerIndex p' + 1 →
      ∀ {z : Fin d → ℤ}, 1 ≤ ‖z‖ → liftPt p z = p' → ∀ (ν' : Fin d),
      ((reflectedGS G h).spacing p) ^ 2 *
          ‖(reflSol h a ν α g (p' + Pi.single ν' 1) - reflSol h a ν α g p') -
            (reflSol h a ν α g (p + Pi.single ν' 1) - reflSol h a ν α g p)‖ ≤
        (B / θ) * (((reflectedGS G h).spacing p) ^ θ * ‖z‖ ^ (1 - θ)) *
          ((decay (agmonRate d / 2) (G.pathDist (foldTo N₀ L k q s c p) (foldTo N₀ L k q s c r)) +
            decay (agmonRate d / 2)
              (G.pathDist (foldTo N₀ L k q s c p') (foldTo N₀ L k q s c r))) *
            ((L : ℝ) ^ (2 * j') * Mf)) := by
  obtain ⟨B, hB, hH⟩ := holder_pair_decay (d := d) (L := L) hd hL
  refine ⟨B, hB, ?_⟩
  intro θ hθ0 hθ1 k N₀ _ ϱ G q s c _ h a ν hν0 hν1 ha α hα hϱ hsep j' hj'1 hj'q r hr g hg Mf
    hMf0 hMf p p' hlay z hz hlift ν'
  set S := reflSetting h hd hL hν0 hν1 ha α hα hϱ hsep hj'1 hj'q r hr g hg with hS
  have h1 := hH hθ0 hθ1 (reflectedGS G h) S hMf0 hMf (mem_reflectedGS_Ω_one h p)
    (mem_reflectedGS_Ω_one h p') hlay hz hlift ν'
  have hd0 : 0 ≤ agmonRate d / 2 := by
    have := agmonRate_pos (show 0 < d by omega)
    positivity
  have h2 := decay_anti_dist hd0 (pathDist_fold_le h p r)
  have h3 := decay_anti_dist hd0 (pathDist_fold_le h p' r)
  have hF : 0 ≤ (L : ℝ) ^ (2 * j') * Mf := by positivity
  have hBθ : 0 ≤ B / θ := by positivity
  have hX : 0 ≤ ((reflectedGS G h).spacing p) ^ θ * ‖z‖ ^ (1 - θ) := by
    have := spacing_pos (reflectedGS G h) (x := p)
    positivity
  refine le_trans (le_of_eq rfl) (h1.trans ?_)
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hBθ hX)
  exact mul_le_mul_of_nonneg_right (add_le_add h2 h3) hF

open scoped Classical in
/-- The part of the even extension `E f` lying over the reflected block `β`. -/
noncomputable def srcPiece (h : FoldSetting G q s c) (j' : ℕ) (β : Torus d (2 * s * L ^ (q - j')))
    (f : G.Ω 1 → ℂ) : (reflectedGS G h).Ω 1 → ℂ :=
  fun p => if jBlock d L (2 * s) q j' (p : Torus d (2 * s * L ^ q)) = β then reflU h f p else 0

theorem sum_srcPiece (h : FoldSetting G q s c) {j' : ℕ} (hj'q : j' ≤ q)
    {y' : Torus d (N₀ * L ^ k)} (f : G.Ω 1 → ℂ)
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y') :
    ∑ β ∈ sourceBlocks N₀ L k q s c j' y', srcPiece h j' β f = reflU h f := by
  classical
  funext p
  rw [Finset.sum_apply]
  simp only [srcPiece]
  rw [Finset.sum_ite_eq]
  by_cases hf : reflU h f p = 0
  · simp [hf]
  · have hf' : f ⟨foldTo N₀ L k q s c p, foldTo_mem_Ω_one h p⟩ ≠ 0 := hf
    have hb := hsupp _ hf'
    have hmem : jBlock d L (2 * s) q j' (p : Torus d (2 * s * L ^ q)) ∈
        sourceBlocks N₀ L k q s c j' y' :=
      (jBlock_mem_sourceBlocks_iff h hj'q y' p).2 hb
    simp [hmem]

theorem reflSol_sum (h : FoldSetting G q s c) (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    {ι : Type*} (T : Finset ι) (g : ι → (reflectedGS G h).Ω 1 → ℂ) (p : Torus d (2 * s * L ^ q)) :
    reflSol h a ν α (∑ i ∈ T, g i) p = ∑ i ∈ T, reflSol h a ν α (g i) p := by
  classical
  unfold reflSol
  rw [Matrix.mulVec_sum]
  by_cases hp : p ∈ (reflectedGS G h).Ω 1
  · simp only [zeroExt, hp, ↓reduceDIte, Finset.sum_apply]
  · simp [zeroExt, hp]

theorem norm_sum_grad_le {ι : Type*} (T : Finset ι) {w : ℝ} (hw : 0 ≤ w) (v : ι → ℂ)
    (v' : Fin d → ι → ℂ) :
    ‖∑ i ∈ T, v i‖ + w * ∑ μ : Fin d, ‖∑ i ∈ T, v' μ i - ∑ i ∈ T, v i‖ ≤
      ∑ i ∈ T, (‖v i‖ + w * ∑ μ : Fin d, ‖v' μ i - v i‖) := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
  refine add_le_add (norm_sum_le _ _) (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun μ _ => ?_) hw)
  rw [← Finset.sum_sub_distrib]
  exact norm_sum_le _ _

/-- **Pointwise bound on the doubled torus for the even extension of a source in one block.** -/
theorem refl_U_le (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)
      {q s : ℕ} {c : Fin d → ℕ} [NeZero s] (h : FoldSetting G q s c) {a : ℕ → ℝ} {ν : ℝ},
      0 ≤ ν → ν * ((L : ℝ) ^ k) ^ 2 ≤ 1 → IsAdmissibleWeights k a →
      ∀ (α : G.Ω 1 → ℂ), (∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) →
      1 ≤ ϱ → (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) →
      ∀ {j' : ℕ} {y' : Torus d (N₀ * L ^ k)}, 1 ≤ j' → j' ≤ k → y' ∈ G.layer j' →
      y' ∈ cubeOf N₀ L k q s c → ∀ (f : G.Ω 1 → ℂ),
      (∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y') →
      ∀ {Mf : ℝ}, 0 ≤ Mf → (∀ z, ‖f z‖ ≤ Mf) → ∀ (p : Torus d (2 * s * L ^ q)),
      ‖reflSol h a ν α (reflU h f) p‖ + (reflectedGS G h).spacing p *
          ∑ μ : Fin d, ‖reflSol h a ν α (reflU h f) (p + Pi.single μ 1) -
            reflSol h a ν α (reflU h f) p‖ ≤
        K * decay (agmonRate d / 2) (G.pathDist (foldTo N₀ L k q s c p) y') *
          ((L : ℝ) ^ (2 * j') * Mf) := by
  classical
  obtain ⟨K2, hK2, hS⟩ := single_source_U_le (d := d) (L := L) hd hL
  refine ⟨2 ^ d * K2, by positivity, ?_⟩
  intro k N₀ _ ϱ G q s c _ h a ν hν0 hν1 ha α hα hϱ hsep j' y' hj'1 hj'k hy' hyc f hsupp Mf hMf0
    hMf p
  have hj'q : j' ≤ q := by
    have h1 := foldTo_unfoldPt h hyc
    have h2 := layerIndex_le h (unfoldPt N₀ L k q s c y')
    rw [h1, G.layerIndex_eq hj'1 hj'k hy'] at h2
    exact h2
  rw [← sum_srcPiece h hj'q f hsupp (y' := y')]
  simp only [reflSol_sum]
  have hw : 0 ≤ (reflectedGS G h).spacing p := (spacing_pos (reflectedGS G h)).le
  refine (norm_sum_grad_le (sourceBlocks N₀ L k q s c j' y') hw
    (fun β => reflSol h a ν α (srcPiece h j' β f) p)
    (fun μ β => reflSol h a ν α (srcPiece h j' β f) (p + Pi.single μ 1))).trans ?_
  have hterm : ∀ β ∈ sourceBlocks N₀ L k q s c j' y',
      ‖reflSol h a ν α (srcPiece h j' β f) p‖ + (reflectedGS G h).spacing p *
          ∑ μ : Fin d, ‖reflSol h a ν α (srcPiece h j' β f) (p + Pi.single μ 1) -
            reflSol h a ν α (srcPiece h j' β f) p‖ ≤
        K2 * decay (agmonRate d / 2) (G.pathDist (foldTo N₀ L k q s c p) y') *
          ((L : ℝ) ^ (2 * j') * Mf) := by
    intro β hβ
    obtain ⟨r, hr1, hr2⟩ := exists_source_pre y' hβ
    have hrl : foldTo N₀ L k q s c r ∈ G.layer j' := by rw [hr1]; exact hy'
    have := hS G h hν0 hν1 ha α hα hϱ hsep hj'1 hj'q r hrl (srcPiece h j' β f)
      (fun x hx => by
        unfold srcPiece at hx
        by_contra hne
        rw [hr2] at hne
        simp only [hne, ↓reduceIte] at hx
        exact hx rfl) hMf0 (fun x => by
        unfold srcPiece
        split_ifs
        · exact hMf _
        · simpa using hMf0) p
    rwa [hr1] at this
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((sourceBlocks N₀ L k q s c j' y').card : ℝ) ≤ 2 ^ d := by
    exact_mod_cast card_sourceBlocks_le h j' y'
  have hnn : 0 ≤ K2 * decay (agmonRate d / 2) (G.pathDist (foldTo N₀ L k q s c p) y') *
      ((L : ℝ) ^ (2 * j') * Mf) := by
    have := decay_nonneg (agmonRate d / 2) (G.pathDist (foldTo N₀ L k q s c p) y')
    positivity
  calc _ ≤ (2 ^ d : ℝ) * (K2 * decay (agmonRate d / 2) (G.pathDist (foldTo N₀ L k q s c p) y') *
        ((L : ℝ) ^ (2 * j') * Mf)) := mul_le_mul_of_nonneg_right hc hnn
    _ = _ := by ring

/-- **Hölder bound on the doubled torus for the even extension of a source in one block.** -/
theorem refl_holder_le (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ}
      (G : GeneratingSet d L N₀ k ϱ)
      {q s : ℕ} {c : Fin d → ℕ} [NeZero s] (h : FoldSetting G q s c) {a : ℕ → ℝ} {ν : ℝ},
      0 ≤ ν → ν * ((L : ℝ) ^ k) ^ 2 ≤ 1 → IsAdmissibleWeights k a →
      ∀ (α : G.Ω 1 → ℂ), (∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) →
      1 ≤ ϱ → (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) →
      ∀ {j' : ℕ} {y' : Torus d (N₀ * L ^ k)}, 1 ≤ j' → j' ≤ k → y' ∈ G.layer j' →
      y' ∈ cubeOf N₀ L k q s c → ∀ (f : G.Ω 1 → ℂ),
      (∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y') →
      ∀ {Mf : ℝ}, 0 ≤ Mf → (∀ z, ‖f z‖ ≤ Mf) → ∀ {p p' : Torus d (2 * s * L ^ q)},
      (reflectedGS G h).layerIndex p ≤ (reflectedGS G h).layerIndex p' + 1 →
      ∀ {z : Fin d → ℤ}, 1 ≤ ‖z‖ → liftPt p z = p' → ∀ (ν' : Fin d),
      ((reflectedGS G h).spacing p) ^ 2 *
          ‖(reflSol h a ν α (reflU h f) (p' + Pi.single ν' 1) - reflSol h a ν α (reflU h f) p') -
            (reflSol h a ν α (reflU h f) (p + Pi.single ν' 1) -
              reflSol h a ν α (reflU h f) p)‖ ≤
        (B / θ) * (((reflectedGS G h).spacing p) ^ θ * ‖z‖ ^ (1 - θ)) *
          ((decay (agmonRate d / 2) (G.pathDist (foldTo N₀ L k q s c p) y') +
            decay (agmonRate d / 2) (G.pathDist (foldTo N₀ L k q s c p') y')) *
            ((L : ℝ) ^ (2 * j') * Mf)) := by
  classical
  obtain ⟨B0, hB0, hS⟩ := single_source_holder_le (d := d) (L := L) hd hL
  refine ⟨2 ^ d * B0, by positivity, ?_⟩
  intro θ hθ0 hθ1 k N₀ _ ϱ G q s c _ h a ν hν0 hν1 ha α hα hϱ hsep j' y' hj'1 hj'k hy' hyc f hsupp
    Mf hMf0 hMf p p' hlay z hz hlift ν'
  have hj'q : j' ≤ q := by
    have h1 := foldTo_unfoldPt h hyc
    have h2 := layerIndex_le h (unfoldPt N₀ L k q s c y')
    rw [h1, G.layerIndex_eq hj'1 hj'k hy'] at h2
    exact h2
  rw [← sum_srcPiece h hj'q f hsupp (y' := y')]
  simp only [reflSol_sum]
  have hsp : 0 ≤ ((reflectedGS G h).spacing p) ^ 2 := by positivity
  have hterm : ∀ β ∈ sourceBlocks N₀ L k q s c j' y',
      ((reflectedGS G h).spacing p) ^ 2 *
          ‖(reflSol h a ν α (srcPiece h j' β f) (p' + Pi.single ν' 1) -
              reflSol h a ν α (srcPiece h j' β f) p') -
            (reflSol h a ν α (srcPiece h j' β f) (p + Pi.single ν' 1) -
              reflSol h a ν α (srcPiece h j' β f) p)‖ ≤
        (B0 / θ) * (((reflectedGS G h).spacing p) ^ θ * ‖z‖ ^ (1 - θ)) *
          ((decay (agmonRate d / 2) (G.pathDist (foldTo N₀ L k q s c p) y') +
            decay (agmonRate d / 2) (G.pathDist (foldTo N₀ L k q s c p') y')) *
            ((L : ℝ) ^ (2 * j') * Mf)) := by
    intro β hβ
    obtain ⟨r, hr1, hr2⟩ := exists_source_pre y' hβ
    have hrl : foldTo N₀ L k q s c r ∈ G.layer j' := by rw [hr1]; exact hy'
    have := hS hθ0 hθ1 G h hν0 hν1 ha α hα hϱ hsep hj'1 hj'q r hrl (srcPiece h j' β f)
      (fun x hx => by
        unfold srcPiece at hx
        by_contra hne
        rw [hr2] at hne
        simp only [hne, ↓reduceIte] at hx
        exact hx rfl) hMf0 (fun x => by
        unfold srcPiece
        split_ifs
        · exact hMf _
        · simpa using hMf0) hlay hz hlift ν'
    rwa [hr1] at this
  have hsum : ((reflectedGS G h).spacing p) ^ 2 *
      ‖(∑ β ∈ sourceBlocks N₀ L k q s c j' y',
            reflSol h a ν α (srcPiece h j' β f) (p' + Pi.single ν' 1) -
          ∑ β ∈ sourceBlocks N₀ L k q s c j' y', reflSol h a ν α (srcPiece h j' β f) p') -
        (∑ β ∈ sourceBlocks N₀ L k q s c j' y',
            reflSol h a ν α (srcPiece h j' β f) (p + Pi.single ν' 1) -
          ∑ β ∈ sourceBlocks N₀ L k q s c j' y', reflSol h a ν α (srcPiece h j' β f) p)‖ ≤
      ∑ β ∈ sourceBlocks N₀ L k q s c j' y', ((reflectedGS G h).spacing p) ^ 2 *
          ‖(reflSol h a ν α (srcPiece h j' β f) (p' + Pi.single ν' 1) -
              reflSol h a ν α (srcPiece h j' β f) p') -
            (reflSol h a ν α (srcPiece h j' β f) (p + Pi.single ν' 1) -
              reflSol h a ν α (srcPiece h j' β f) p)‖ := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hsp
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact norm_sum_le _ _
  refine hsum.trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((sourceBlocks N₀ L k q s c j' y').card : ℝ) ≤ 2 ^ d := by
    exact_mod_cast card_sourceBlocks_le h j' y'
  have hnn : 0 ≤ (B0 / θ) * (((reflectedGS G h).spacing p) ^ θ * ‖z‖ ^ (1 - θ)) *
          ((decay (agmonRate d / 2) (G.pathDist (foldTo N₀ L k q s c p) y') +
            decay (agmonRate d / 2) (G.pathDist (foldTo N₀ L k q s c p') y')) *
            ((L : ℝ) ^ (2 * j') * Mf)) := by
    have h1 := decay_nonneg (agmonRate d / 2) (G.pathDist (foldTo N₀ L k q s c p) y')
    have h2 := decay_nonneg (agmonRate d / 2) (G.pathDist (foldTo N₀ L k q s c p') y')
    have h3 := spacing_pos (reflectedGS G h) (x := p)
    have h4 : (0 : ℝ) < ‖z‖ := by linarith
    positivity
  calc _ ≤ (2 ^ d : ℝ) * ((B0 / θ) * (((reflectedGS G h).spacing p) ^ θ * ‖z‖ ^ (1 - θ)) *
          ((decay (agmonRate d / 2) (G.pathDist (foldTo N₀ L k q s c p) y') +
            decay (agmonRate d / 2) (G.pathDist (foldTo N₀ L k q s c p') y')) *
            ((L : ℝ) ^ (2 * j') * Mf))) := mul_le_mul_of_nonneg_right hc hnn
    _ = _ := by ring

end Balaban.Reflection
