/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0HaloAffine
public import Balaban.Polymer.BoxTransport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0BoxLift`: the walk-halo pieces on two tori

The halo pieces of the all-plus site and bond functions (`KF0F1Assembly`) are the same functions on
two tori when the halo lies in a box of `ℤ^d` that does not wrap around either torus. The box map
`boxMap ℓ ℓ'` (centred representatives) carries nearest-neighbour steps between sites of the box
(`boxMap_step_iff`, `boxMap_add_step`), walks inside the box (`pathPt_boxMap`), their halos and
endpoints (`walkHalo_boxMap`), and so the halo term of a coefficient family
(`kf0HaloTerm_boxMap`): the walk-series indices with halo `H` on the first torus and with halo
`ι '' H` on the second are the same indices, with equal terms. The consequences for the site, source
and bond pieces are `f1SiteHalo_boxMap`, `f1SiteSrcHalo_boxMap`, `f1BondHalo_boxMap`.
-/

@[expose] public section

open Finset Balaban.Green Balaban.LargeField Balaban.LargeField.KF0F1 Balaban.Polymer

namespace Balaban.KF0Lift

section Steps

variable {d : ℕ} {R m m' : ℕ}

/-- A nearest-neighbour step between two sites of the box is carried by `boxMap`. -/
theorem boxMap_step_iff (hm : 2 * R + 1 < m) (hm' : 2 * R + 1 < m') {a b : Torus d m}
    (ha : InBox d R m a) (hb : InBox d R m b) (μ : Fin d) :
    b = a + Pi.single μ 1 ↔ boxMap m m' b = boxMap m m' a + Pi.single μ 1 := by
  rw [step_iff hm ha hb, step_iff hm' (inBox_boxMap hm' ha) (inBox_boxMap hm' hb)]
  have e1 : (fun ν => (boxMap m m' b ν).valMinAbs) = fun ν => (b ν).valMinAbs :=
    funext (valMinAbs_boxMap hm' hb)
  have e2 : (fun ν => (boxMap m m' a ν).valMinAbs) = fun ν => (a ν).valMinAbs :=
    funext (valMinAbs_boxMap hm' ha)
  rw [e1, e2]

theorem intToTorus_stepVec_true (μ : Fin d) :
    intToTorus d m (stepVec d (μ, true)) = Pi.single μ 1 := by
  ext ν; by_cases h : ν = μ <;> simp [stepVec, intToTorus_apply, h]

theorem intToTorus_stepVec_false (μ : Fin d) :
    intToTorus d m (stepVec d (μ, false)) = -Pi.single μ 1 := by
  ext ν; by_cases h : ν = μ <;> simp [stepVec, intToTorus_apply, h]

/-- A walk step between two sites of the box is carried by `boxMap`. -/
theorem boxMap_add_step (hm : 2 * R + 1 < m) (hm' : 2 * R + 1 < m') {a : Torus d m}
    (ha : InBox d R m a) (s : Fin d × Bool) (hb : InBox d R m (a + intToTorus d m (stepVec d s))) :
    boxMap m m' (a + intToTorus d m (stepVec d s)) =
      boxMap m m' a + intToTorus d m' (stepVec d s) := by
  obtain ⟨μ, b⟩ := s
  cases b
  · rw [intToTorus_stepVec_false] at hb ⊢
    rw [intToTorus_stepVec_false]
    have h1 : a = (a + -Pi.single μ 1) + Pi.single μ 1 := by abel
    have := (boxMap_step_iff hm hm' hb ha μ).1 h1
    rw [this]; abel
  · rw [intToTorus_stepVec_true] at hb ⊢
    rw [intToTorus_stepVec_true]
    exact (boxMap_step_iff hm hm' ha hb μ).1 rfl

theorem pathPt_succ_eq (x : Torus d m) (w : KF0Walk d) {k : ℕ} (hk : k < w.1) :
    pathPt x w (k + 1) = pathPt x w k + intToTorus d m (stepVec d (w.2 ⟨k, hk⟩)) := by
  unfold pathPt
  rw [Finset.sum_range_succ, map_add, add_assoc]
  simp [walkStep, hk]

/-- **A walk inside the box is carried by `boxMap`.** -/
theorem pathPt_boxMap (hm : 2 * R + 1 < m) (hm' : 2 * R + 1 < m') (x : Torus d m)
    (w : KF0Walk d) (hbox : ∀ k ≤ w.1, InBox d R m (pathPt x w k)) :
    ∀ k ≤ w.1, pathPt (boxMap m m' x) w k = boxMap m m' (pathPt x w k) := by
  intro k
  induction k with
  | zero => intro _; simp [pathPt_zero]
  | succ k ih =>
    intro hk
    have hk' : k < w.1 := hk
    rw [pathPt_succ_eq _ w hk', ih hk'.le, pathPt_succ_eq x w hk']
    have hb := hbox (k + 1) hk
    rw [pathPt_succ_eq x w hk'] at hb
    rw [boxMap_add_step hm hm' (hbox k hk'.le) _ hb]

end Steps

section Halo

variable {d : ℕ} {R m m' : ℕ} {ι : Type} [Fintype ι]

/-- **A halo inside the box is carried by `boxMap`**, with its anchors and the endpoints of its
walks. -/
theorem walkHalo_boxMap (hm : 2 * R + 1 < m) (hm' : 2 * R + 1 < m') (x : ι → Torus d m)
    (ω : ι → KF0Walk d) (hbox : ∀ a ∈ walkHalo x ω, InBox d R m a) :
    walkHalo (fun i => boxMap m m' (x i)) ω = (walkHalo x ω).image (boxMap m m') ∧
      ∀ i, walkEnd (boxMap m m' (x i)) (ω i) = boxMap m m' (walkEnd (x i) (ω i)) := by
  have hp : ∀ i, ∀ k ≤ (ω i).1, pathPt (boxMap m m' (x i)) (ω i) k =
      boxMap m m' (pathPt (x i) (ω i) k) := fun i =>
    pathPt_boxMap hm hm' (x i) (ω i) (fun k hk => hbox _ (pathPt_mem_walkHalo x ω i hk))
  refine ⟨?_, fun i => ?_⟩
  · ext a'
    rw [mem_walkHalo, Finset.mem_image]
    constructor
    · rintro ⟨i, k, hk, rfl⟩
      exact ⟨pathPt (x i) (ω i) k, pathPt_mem_walkHalo x ω i hk, (hp i k hk).symm⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨i, k, hk, rfl⟩ := mem_walkHalo.1 ha
      exact ⟨i, k, hk, hp i k hk⟩
  · have := hp i _ le_rfl
    rwa [pathPt_length, pathPt_length] at this

end Halo

section HaloTerm

variable {d : ℕ} {R m m' : ℕ} [NeZero m] [NeZero m'] {W : Type*} [NormedAddCommGroup W]
  [NormedSpace ℝ W] {D : ℕ}

/-- **The halo term is the same function on two tori** for a halo inside the box: with anchors
`x_j` in the box and `ψ' ∘ ι = ψ` on `H`, the term of the halo `ι '' H` at the anchors `ι x_j`
on the second torus is the term of the halo `H` at the anchors `x_j` on the first. The index sets
`{a : halo a = H}` and `{a : halo' a = ι '' H}` coincide (`walkHalo_boxMap` in both directions) and
the terms agree (the endpoints of the walks correspond). -/
theorem kf0HaloTerm_boxMap (hm : 2 * R + 1 < m) (hm' : 2 * R + 1 < m') (ν β : ℝ)
    (x : Fin D → Torus d m) (hx : ∀ j, InBox d R m (x j)) (ℓc : Fin D → W →L[ℝ] ℝ)
    (c : (Fin D → ℕ) → ℝ) (H : Finset (Torus d m)) (hH : ∀ y ∈ H, InBox d R m y)
    (ψ : Torus d m → W) (ψ' : Torus d m' → W) (hψ : ∀ y ∈ H, ψ' (boxMap m m' y) = ψ y) :
    kf0HaloTerm d m' ν β (fun j => boxMap m m' (x j)) ℓc c (H.image (boxMap m m')) ψ' =
      kf0HaloTerm d m ν β x ℓc c H ψ := by
  unfold kf0HaloTerm haloPiece
  have hH' : ∀ a ∈ H.image (boxMap m m'), InBox d R m' a := fun a ha => by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 ha
    exact inBox_boxMap hm' (hH y hy)
  have hback : (H.image (boxMap m m')).image (boxMap m' m) = H := by
    rw [Finset.image_image]
    conv_rhs => rw [← Finset.image_id (s := H)]
    exact Finset.image_congr fun y hy => boxMap_boxMap hm' (hH y hy)
  have hS : kf0WalkSeriesHalo (fun j => boxMap m m' (x j)) ⁻¹' {H.image (boxMap m m')} =
      kf0WalkSeriesHalo x ⁻¹' {H} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro ha
      have h1 := (walkHalo_boxMap (m := m') (m' := m) hm' hm
        (fun s : KF0Slot a.1 => boxMap m m' (x s.1)) a.2 (by
          intro b hb
          have : walkHalo (fun s : KF0Slot a.1 => boxMap m m' (x s.1)) a.2 =
              H.image (boxMap m m') := ha
          rw [this] at hb
          exact hH' b hb)).1
      have h2 : (fun s : KF0Slot a.1 => boxMap m' m (boxMap m m' (x s.1))) =
          fun s => x s.1 := funext fun s => boxMap_boxMap hm' (hx s.1)
      rw [h2] at h1
      have : walkHalo (fun s : KF0Slot a.1 => boxMap m m' (x s.1)) a.2 =
          H.image (boxMap m m') := ha
      rw [this, hback] at h1
      exact h1
    · intro ha
      have h1 := (walkHalo_boxMap hm hm' (fun s : KF0Slot a.1 => x s.1) a.2 (by
          intro b hb
          have : walkHalo (fun s : KF0Slot a.1 => x s.1) a.2 = H := ha
          rw [this] at hb
          exact hH b hb)).1
      have : walkHalo (fun s : KF0Slot a.1 => x s.1) a.2 = H := ha
      rw [this] at h1
      exact h1
  rw [hS]
  refine tsum_congr fun a => ?_
  have ha : kf0WalkSeriesHalo x a.1 = H := a.2
  have hbox : ∀ b ∈ walkHalo (fun s : KF0Slot a.1.1 => x s.1) a.1.2, InBox d R m b := by
    intro b hb
    have : walkHalo (fun s : KF0Slot a.1.1 => x s.1) a.1.2 = H := ha
    rw [this] at hb
    exact hH b hb
  obtain ⟨-, hend⟩ := walkHalo_boxMap hm hm' (fun s : KF0Slot a.1.1 => x s.1) a.1.2 hbox
  simp only [kf0WalkSeriesTerm, kf0WalkTerm]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [hend s]
  have hmem : walkEnd (x s.1) (a.1.2 s) ∈ H := by
    have h3 : walkEnd (x s.1) (a.1.2 s) ∈ kf0WalkSeriesHalo x a.1 :=
      walkEnd_mem_walkHalo (fun s : KF0Slot a.1.1 => x s.1) a.1.2 s
    rwa [ha] at h3
  rw [hψ _ hmem]

end HaloTerm

section F1

open SphereChart Balaban.LargeField.KF0AllPlus

variable {d N n ℓ ℓ' R : ℕ} [NeZero ℓ] [NeZero ℓ'] {h : EuclideanSpace ℝ (Fin N)}

/-- The site pieces are the same functions on two tori for a halo inside the box. -/
theorem f1SiteHalo_boxMap (hm : 2 * R + 1 < ℓ) (hm' : 2 * R + 1 < ℓ')
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ) (src : Torus d ℓ → Fin N → ℝ)
    (src' : Torus d ℓ' → Fin N → ℝ) (x : Torus d ℓ) (hx : InBox d R ℓ x)
    (hsrc : src' (boxMap ℓ ℓ' x) = src x) (H : Finset (Torus d ℓ))
    (hH : ∀ y ∈ H, InBox d R ℓ y) (ψ : Torus d ℓ → perp h) (ψ' : Torus d ℓ' → perp h)
    (hψ : ∀ y ∈ H, ψ' (boxMap ℓ ℓ' y) = ψ y) :
    f1SiteHalo e β ν src' (boxMap ℓ ℓ' x) (H.image (boxMap ℓ ℓ')) ψ' =
      f1SiteHalo e β ν src x H ψ := by
  unfold f1SiteHalo
  have hN : f1Nrm src' h (boxMap ℓ ℓ' x) = f1Nrm src h x := by simp [f1Nrm, hsrc]
  have hL : f1Lin e src' (boxMap ℓ ℓ' x) = f1Lin e src x := by
    funext j; simp only [f1Lin]; rw [hsrc]
  rw [hN, hL]
  exact kf0HaloTerm_boxMap hm hm' ν β (fun _ : Fin n => x) (fun _ => hx) (tcoord e) _ H hH ψ ψ' hψ

/-- The source pieces are the same functions on two tori for a halo inside the box. -/
theorem f1SiteSrcHalo_boxMap (hm : 2 * R + 1 < ℓ) (hm' : 2 * R + 1 < ℓ')
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ) (x : Torus d ℓ) (hx : InBox d R ℓ x)
    (i : Fin N) (H : Finset (Torus d ℓ)) (hH : ∀ y ∈ H, InBox d R ℓ y) (ψ : Torus d ℓ → perp h)
    (ψ' : Torus d ℓ' → perp h) (hψ : ∀ y ∈ H, ψ' (boxMap ℓ ℓ' y) = ψ y) :
    f1SiteSrcHalo e β ν (boxMap ℓ ℓ' x) i (H.image (boxMap ℓ ℓ')) ψ' =
      f1SiteSrcHalo e β ν x i H ψ := by
  unfold f1SiteSrcHalo
  exact kf0HaloTerm_boxMap hm hm' ν β (fun _ : Fin n => x) (fun _ => hx) (tcoord e) _ H hH ψ ψ' hψ

/-- The bond pieces are the same functions on two tori for a halo inside the box. -/
theorem f1BondHalo_boxMap (hm : 2 * R + 1 < ℓ) (hm' : 2 * R + 1 < ℓ')
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ) (x : Torus d ℓ) (μ : Fin d)
    (hx : InBox d R ℓ x) (hx' : InBox d R ℓ (x + Pi.single μ 1))
    (H : Finset (Torus d ℓ)) (hH : ∀ y ∈ H, InBox d R ℓ y) (ψ : Torus d ℓ → perp h)
    (ψ' : Torus d ℓ' → perp h) (hψ : ∀ y ∈ H, ψ' (boxMap ℓ ℓ' y) = ψ y) :
    f1BondHalo e β ν (boxMap ℓ ℓ' x) μ (H.image (boxMap ℓ ℓ')) ψ' =
      f1BondHalo e β ν x μ H ψ := by
  unfold f1BondHalo
  have hstep : boxMap ℓ ℓ' (x + Pi.single μ 1) = boxMap ℓ ℓ' x + Pi.single μ 1 :=
    (boxMap_step_iff hm hm' hx hx' μ).1 rfl
  have hanch : (bondAnchor n (boxMap ℓ ℓ' x + Pi.single μ 1) (boxMap ℓ ℓ' x) :
      Fin (n + n) → Torus d ℓ') =
      fun j => boxMap ℓ ℓ' (bondAnchor n (x + Pi.single μ 1) x j) := by
    funext j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j <;>
      simp only [bondAnchor, Fin.append_left, Fin.append_right, hstep]
  rw [hanch]
  refine kf0HaloTerm_boxMap hm hm' ν β (bondAnchor n (x + Pi.single μ 1) x) (fun j => ?_)
    (bondEll e) _ H hH ψ ψ' hψ
  refine Fin.addCases (fun a => ?_) (fun a => ?_) j <;>
    simp only [bondAnchor, Fin.append_left, Fin.append_right] <;> assumption

end F1

end Balaban.KF0Lift
