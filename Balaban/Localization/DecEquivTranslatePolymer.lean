/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivTranslate
public import Balaban.Localization.DecEquivTerms
public import Balaban.Localization.DecEquivTranslateStep
public import Balaban.Fluctuation.InteractionSymmLat

/-!
# Translations are compatible with the polymers of a level set

For a level set `G` (`IsLevel G n`) and a translation `x ↦ x + t` of the fine torus, the two
fields of `PolymerSymm` (at the centres of the cover, which all lie in the layer `n`) hold when
* `L ^ (n + m₀ + m₁) ∣ t_μ` for all `μ` (the cells of side `a_n = L ^ (n + m₀ + m₁)` are
  translated to cells, and the grid of the bases of the cubes `□'` is preserved), and
* `L ^ m₀ ∣ N₁` (the side `a_n` divides the side of the torus, as in `cellSide_dvd`).

This is stated for level sets only.  Covariance of the output terms of a step is not proved here
beyond the term covariance at the translation of the landed step.
-/

@[expose] public section

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

section Boxes

variable {d n : ℕ} [NeZero n]

omit [NeZero n] in
theorem mem_box_add_iff (b t x : Torus d n) (s : ℕ) :
    x + t ∈ box (b + t) s ↔ x ∈ box b s := by
  unfold box
  simp only [Set.mem_ofPred_eq]
  refine exists_congr fun w => and_congr_right fun _ => ?_
  rw [add_right_comm, add_left_inj]

theorem cbase_add_translate {a : ℕ} (ha : a ∣ n) (y t : Torus d n) (ht : ∀ μ, a ∣ (t μ).val) :
    cbase a (y + t) = cbase a y + t := by
  rw [cbase_eq_sub, cbase_eq_sub]
  have h : (fun μ => ((y + t : Torus d n) μ).val % a) = fun μ => (y μ).val % a := by
    funext μ
    rw [Pi.add_apply, ZMod.val_add, Nat.mod_mod_of_dvd _ ha, Nat.add_mod,
      Nat.mod_eq_zero_of_dvd (ht μ), add_zero, Nat.mod_mod]
  rw [h]; abel

theorem aligned_add_iff {a : ℕ} (ha : a ∣ n) (b t : Torus d n) (ht : ∀ μ, a ∣ (t μ).val) :
    Aligned a (b + t) ↔ Aligned a b :=
  forall_congr' fun μ => mod_zero_add_iff ha (b μ) (t μ) (ht μ)

end Boxes

section Level

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {n m₀ : ℕ}

theorem cellOf_translate {j : ℕ} (hj : j ≤ K) (hN : L ^ m₀ ∣ N₁) (y t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (j + m₀ + m₁) ∣ (t μ).val) (x : CTorus d L N₁ m₁ K) :
    x + t ∈ cellOf L m₀ m₁ (j, y + t) ↔ x ∈ cellOf L m₀ m₁ (j, y) := by
  have hd : cellSide L m₀ m₁ j ∣ (N₁ * L ^ m₁) * L ^ K := cellSide_dvd hN hj
  unfold cellOf
  simp only
  rw [cbase_add_translate hd y t ht]
  exact mem_box_add_iff _ t x _

theorem dcubes_translate (hG : IsLevel G n) (hn : n ≤ K) (hN : L ^ m₀ ∣ N₁)
    (y t : CTorus d L N₁ m₁ K) (ht : ∀ μ, L ^ (n + m₀ + m₁) ∣ (t μ).val)
    (b : CTorus d L N₁ m₁ K) :
    b + t ∈ Dcubes G m₀ (n, y + t) ↔ b ∈ Dcubes G m₀ (n, y) := by
  have hd : cellSide L m₀ m₁ n ∣ (N₁ * L ^ m₁) * L ^ K := cellSide_dvd hN hn
  have ht' : ∀ μ, cellSide L m₀ m₁ n ∣ (t μ).val := ht
  unfold Dcubes
  simp only [Set.mem_ofPred_eq]
  refine and_congr (aligned_add_iff hd b t ht') (and_congr ?_ ?_)
  · constructor
    · intro h x hx
      exact (mem_box_add_iff b t x _).1 (h ((cellOf_translate hn hN y t ht x).2 hx))
    · intro h z hz
      obtain ⟨x, rfl⟩ : ∃ x, z = x + t := ⟨z - t, by abel⟩
      exact (mem_box_add_iff b t x _).2 (h ((cellOf_translate hn hN y t ht x).1 hz))
  · exact ⟨fun _ x hx => (hG.mem_layer x), fun _ x hx => (hG.mem_layer x)⟩

/-- **The sets `D(P)` are translated** by a translation of a level set: for a centre of the layer
`n`, `D(n, y₀ + t) = D(n, y₀) + t` when `L ^ (n + m₀ + m₁) ∣ t_μ` and `L ^ m₀ ∣ N₁`. -/
theorem Dsites_translate (hG : IsLevel G n) (hn : n ≤ K) (hN : L ^ m₀ ∣ N₁)
    (y t : CTorus d L N₁ m₁ K) (ht : ∀ μ, L ^ (n + m₀ + m₁) ∣ (t μ).val) :
    Dsites G m₀ (n, y + t) = (Equiv.addRight t) '' Dsites G m₀ (n, y) := by
  ext z
  obtain ⟨x, rfl⟩ : ∃ x, z = x + t := ⟨z - t, by abel⟩
  rw [show x + t = (Equiv.addRight t) x from rfl, (Equiv.addRight t).injective.mem_set_image]
  unfold Dsites
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨b, hb, hx⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + t := ⟨b - t, by abel⟩
    exact ⟨b', (dcubes_translate hG hn hN y t ht b').1 hb, (mem_box_add_iff b' t x _).1 hx⟩
  · rintro ⟨b, hb, hx⟩
    exact ⟨b + t, (dcubes_translate hG hn hN y t ht b).2 hb, (mem_box_add_iff b t x _).2 hx⟩

/-- **(T2') Translations are compatible with the polymers of a level set.** -/
theorem PolymerSymm.ofTranslate (hG : IsLevel G n) (hN : L ^ m₀ ∣ N₁)
    (t : CTorus d L N₁ m₁ K) (ht : ∀ μ, L ^ (n + m₀ + m₁) ∣ (t μ).val) :
    PolymerSymm G m₀ (Equiv.addRight t) (translateCentres t) where
  pset := fun q hq x => by
    have hqn : q.1 = n := fst_eq_of_mem_cubeIdx hG hq
    have hK : q.1 ≤ K := ((mem_cubeIdx G).1 hq).1.2
    have ht' : ∀ μ, L ^ (q.1 + m₁) ∣ (t μ).val := fun μ => by
      rw [hqn]; exact (pow_dvd_pow L (by omega)).trans (ht μ)
    exact Pset_translate hK q.2 t x ht'
  dsites := fun q hq => by
    have hqn : q.1 = n := fst_eq_of_mem_cubeIdx hG hq
    have hK : n ≤ K := hqn ▸ ((mem_cubeIdx G).1 hq).1.2
    obtain ⟨j, y⟩ := q
    simp only at hqn
    subst hqn
    exact Dsites_translate hG hK hN y t ht

end Level

/-! ### The landed step -/

section Step

open Balaban.Inhabited Balaban.Inhabited.LevelStep Balaban.Analysis

variable (m₁ k : ℕ) (ϱ : ℝ) [NeZero (3 : ℕ)]

omit [NeZero (3 : ℕ)] in
theorem stepVec_dvd_polymer (μ : Fin 3) :
    3 ^ (k + 1 + 0 + m₁) ∣ (stepVec m₁ k μ).val := by
  simpa only [Nat.add_zero] using stepVec_dvd m₁ k μ

/-- **`PolymerSymm` is inhabited at a non-identity translation**: at the top level set of the step
(`d = L = N₁ = 3`, `m₀ = 0`), the translation by `stepVec` is a nonzero element of the torus and
is compatible with the polymers.  (`m₀ = 0` is the only value for which `stepVec` is divisible by
the cell side `3 ^ (k + 1 + m₀ + m₁)`; for `m₀ ≥ 1` the divisibility forces `t = 0`.) -/
theorem polymerSymm_translate_lvTop :
    (Equiv.addRight (stepVec m₁ k) : Equiv.Perm (CTorus 3 3 3 m₁ (k + 1))) ≠ 1 ∧
      Nonempty (PolymerSymm (lvTop 3 m₁ k ϱ) 0 (Equiv.addRight (stepVec m₁ k))
        (translateCentres (stepVec m₁ k))) :=
  ⟨translate_ne_one m₁ k,
    ⟨PolymerSymm.ofTranslate isLevel_lvTop (by simp) _ (stepVec_dvd_polymer m₁ k)⟩⟩

/-- **Covariance of the connected families at a non-identity translation of the step.** -/
theorem connFams_translate_lvTop (S : LatSymm (lvTop 3 m₁ k ϱ) (lvTop 3 m₁ k ϱ)
      (Equiv.addRight (stepVec m₁ k))) (X₁ Y : Set (CTorus 3 3 3 m₁ (k + 1))) :
    let G := lvTop 3 m₁ k ϱ
    let CS := CoverSymm.ofTranslate (G := G) isLevel_lvTop (stepVec m₁ k) (stepVec_dvd m₁ k)
    let κ : (coverOf G).cubeIdx ≃ (coverOf G).cubeIdx :=
      Equiv.subtypeEquiv CS.τ fun q => (CS.idx q).symm
    connFams (fun i : (coverOf G).cubeIdx => i.1) G 0
        ((Equiv.addRight (stepVec m₁ k)) '' X₁) ((Equiv.addRight (stepVec m₁ k)) '' Y) =
      (connFams (fun i : (coverOf G).cubeIdx => i.1) G 0 X₁ Y).map
        ⟨Finset.map κ.toEmbedding, Finset.map_injective _⟩ := by
  intro G CS κ
  classical
  exact connFams_relabel (fun i : (coverOf G).cubeIdx => i.1) (fun i : (coverOf G).cubeIdx => i.1)
    κ (fun _ => rfl) (fun i => i.2)
    (PolymerSymm.ofTranslate isLevel_lvTop (by simp) _ (stepVec_dvd_polymer m₁ k)) S X₁ Y

/-- **Covariance of the expansion terms `𝓔(X, Y)` at a non-identity translation of the step**:
the term of the translated function at the translated sets and the translated point equals the
original term. -/
theorem evTerm_translate_lvTop (S : LatSymm (lvTop 3 m₁ k ϱ) (lvTop 3 m₁ k ϱ)
      (Equiv.addRight (stepVec m₁ k))) {R : ℝ} (hR : 1 < R) (X₁ Y : Set (CTorus 3 3 3 m₁ (k + 1)))
    {U U' : Type*} {F : U → ((coverOf (lvTop 3 m₁ k ϱ)).cubeIdx → ℂ) → ℂ}
    {F' : U' → ((coverOf (lvTop 3 m₁ k ϱ)).cubeIdx → ℂ) → ℂ} {u : U} {u' : U'} :
    let G := lvTop 3 m₁ k ϱ
    let CS := CoverSymm.ofTranslate (G := G) isLevel_lvTop (stepVec m₁ k) (stepVec_dvd m₁ k)
    let κ : (coverOf G).cubeIdx ≃ (coverOf G).cubeIdx :=
      Equiv.subtypeEquiv CS.τ fun q => (CS.idx q).symm
    AnalyticOnNhd ℂ (F u) (polydisc (0 : (coverOf G).cubeIdx → ℂ) (fun _ => R)) →
    AnalyticOnNhd ℂ (F' u') (polydisc (0 : (coverOf G).cubeIdx → ℂ) (fun _ => R)) →
    (∀ s ∈ unitCube (coverOf G).cubeIdx, F' u' s = F u (s ∘ κ)) →
    evTerm (fun i : (coverOf G).cubeIdx => i.1) G 0 ((Equiv.addRight (stepVec m₁ k)) '' X₁) F'
        ((Equiv.addRight (stepVec m₁ k)) '' Y) u' =
      evTerm (fun i : (coverOf G).cubeIdx => i.1) G 0 X₁ F Y u := by
  intro G CS κ hF hF' hff
  classical
  exact evTerm_relabel (fun i : (coverOf G).cubeIdx => i.1) (fun i : (coverOf G).cubeIdx => i.1)
    κ hR (PolymerSymm.ofTranslate isLevel_lvTop (by simp) _ (stepVec_dvd_polymer m₁ k)) S
    (fun _ => rfl) (fun i => i.2) X₁ Y hF hF' hff

/-- **The decoupling parameters of a translated polymer system are the translated parameters**
(the consumer `extParams_sym` of `InteractionSymmLat` at the translation of the step). -/
theorem extParams_translate_lvTop (X₁ X₁' : Finset (CTorus 3 3 3 m₁ (k + 1)))
    (hX : (↑X₁' : Set (CTorus 3 3 3 m₁ (k + 1))) =
      (Equiv.addRight (stepVec m₁ k)) '' (↑X₁ : Set (CTorus 3 3 3 m₁ (k + 1))))
    (s' : ParIdx (lvTop 3 m₁ k ϱ) (↑X₁' : Set (CTorus 3 3 3 m₁ (k + 1))) → ℂ) :
    let G := lvTop 3 m₁ k ϱ
    let CS := CoverSymm.ofTranslate (G := G) isLevel_lvTop (stepVec m₁ k) (stepVec_dvd m₁ k)
    extParams G (↑X₁' : Set (CTorus 3 3 3 m₁ (k + 1))) s' =
      CS.par (extParams G (↑X₁ : Set (CTorus 3 3 3 m₁ (k + 1)))
        (s' ∘ parEquiv CS (PolymerSymm.ofTranslate isLevel_lvTop (by simp) _
          (stepVec_dvd_polymer m₁ k)) hX)) :=
  extParams_sym _ _ hX s'

/-- **The old all-centres `pset` condition does hold at the step translation** (so a nonzero
translation can satisfy it): for every centre `(j, y₀)`, `x + t ∈ P(j, y₀ + t) ↔ x ∈ P(j, y₀)`.
For `j ≤ k + 1` this is `Pset_translate`; for `j ≥ k + 2` the cube side `3 ^ (j + m₁)` is at least
the side of the torus and `P(j, y₀)` is the whole torus. -/
theorem pset_all_centres_translate_stepVec (j : ℕ) (y x : CTorus 3 3 3 m₁ (k + 1)) :
    x + stepVec m₁ k ∈ Pset m₁ (j, y + stepVec m₁ k) ↔ x ∈ Pset m₁ (j, y) := by
  by_cases hj : j ≤ k + 1
  · refine Pset_translate hj y _ x fun μ => ?_
    exact (pow_dvd_pow 3 (by omega)).trans (stepVec_dvd m₁ k μ)
  · have hall : ∀ z w : CTorus 3 3 3 m₁ (k + 1), z ∈ Pset m₁ (j, w) := by
      intro z w μ
      have hlt : ∀ v : CTorus 3 3 3 m₁ (k + 1), (v μ).val / 3 ^ (j + m₁) = 0 := fun v => by
        apply Nat.div_eq_of_lt
        refine lt_of_lt_of_le (ZMod.val_lt (v μ)) ?_
        have : (3 * 3 ^ m₁) * 3 ^ (k + 1) = 3 ^ (k + 2 + m₁) := by ring
        rw [this]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hlt, hlt]
    exact ⟨fun _ => hall _ _, fun _ => hall _ _⟩

end Step

end Balaban.Localization.DecEquiv
