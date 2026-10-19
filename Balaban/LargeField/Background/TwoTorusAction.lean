/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusRegField
public import Balaban.LargeField.LF1.Avg
public import Balaban.LargeField.Operators.MainAction

/-!
# Sums over corresponding sets of sites of two tori

For finite sets `X₁`, `X₂` of sites of two tori that correspond (`PtCorr`) and have the margin `2`
in the box, and fields `φ₁`, `φ₂` that agree at corresponding sites, the sums `∑_{x ∈ X} ‖φ(x) - h‖²`,
the bond energies `bondE`, and `starBondE` agree.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField

section Sites

variable {d ℓ₁ ℓ₂ : ℕ} [NeZero ℓ₁] [NeZero ℓ₂] {cc : Fin d → ℤ}

omit [NeZero ℓ₂] in
theorem liftNear_add_single (y : Torus d ℓ₁) (hy : InBoxK 1 ℓ₁ ℓ₂ cc (liftNear cc y)) (μ : Fin d) :
    liftNear cc (y + Pi.single μ 1) = liftNear cc y + Pi.single μ 1 := by
  have e : y + Pi.single μ 1 = zcast ℓ₁ (liftNear cc y + Pi.single μ 1) := by
    rw [zcast_add_single, zcast_liftNear]
  rw [e]
  exact liftNear_zcast (fun μ' => (inBox_two_mul_lt (hy.add_single μ).inBox μ').1)

omit [NeZero ℓ₂] in
theorem liftNear_sub_single (y : Torus d ℓ₁) (hy : InBoxK 1 ℓ₁ ℓ₂ cc (liftNear cc y)) (μ : Fin d) :
    liftNear cc (y - Pi.single μ 1) = liftNear cc y - Pi.single μ 1 := by
  have e : y - Pi.single μ 1 = zcast ℓ₁ (liftNear cc y - Pi.single μ 1) := by
    rw [zcast_sub_single, zcast_liftNear]
  rw [e]
  exact liftNear_zcast (fun μ' => (inBox_two_mul_lt (hy.sub_single μ).inBox μ').1)

/-- The sum over corresponding finite sets of sites. -/
theorem sum_sites {γ : Type*} [AddCommMonoid γ] (X₁ : Finset (Torus d ℓ₁)) (X₂ : Finset (Torus d ℓ₂))
    (hm₁ : ∀ x ∈ X₁, InBox ℓ₁ ℓ₂ cc (liftNear cc x)) (hm₂ : ∀ x ∈ X₂, InBox ℓ₁ ℓ₂ cc (liftNear cc x))
    (hiff : ∀ x₁ x₂, PtCorr cc x₁ x₂ → (x₁ ∈ X₁ ↔ x₂ ∈ X₂)) (f₁ : Torus d ℓ₁ → γ)
    (f₂ : Torus d ℓ₂ → γ) (hf : ∀ x₁ x₂, PtCorr cc x₁ x₂ → x₁ ∈ X₁ → f₁ x₁ = f₂ x₂) :
    ∑ x ∈ X₁, f₁ x = ∑ x ∈ X₂, f₂ x := by
  refine sum_of_rel X₁ X₂ (PtCorr cc) f₁ f₂ ?_ ?_ (fun a b b' h h' => ptCorr_right_unique h h')
    (fun a a' b h h' => ptCorr_left_unique h h') (fun a b ha _ h => hf a b h ha)
  · intro x hx
    have hp := ptCorr_transp (m₂ := ℓ₂) (hm₁ x hx)
    exact ⟨_, (hiff _ _ hp).1 hx, hp⟩
  · intro x hx
    have hp := ptCorr_transp (m₁ := ℓ₂) (m₂ := ℓ₁) (hm₂ x hx).symm
    exact ⟨_, (hiff _ _ (ptCorr_symm hp)).2 hx, ptCorr_symm hp⟩

omit [NeZero ℓ₂] in
theorem margin_edge {X : Finset (Torus d ℓ₁)}
    (hX2 : ∀ x ∈ X, InBoxK 2 ℓ₁ ℓ₂ cc (liftNear cc x)) {x : Torus d ℓ₁} {μ : Fin d}
    (hx : x ∈ X ∨ x + Pi.single μ 1 ∈ X) : InBoxK 1 ℓ₁ ℓ₂ cc (liftNear cc x) := by
  rcases hx with h | h
  · exact (hX2 x h).mono (by omega)
  · have hy := (hX2 _ h).mono (show 1 ≤ 2 by omega)
    have e := liftNear_sub_single (x + Pi.single μ 1) hy μ
    rw [add_sub_cancel_right] at e
    rw [e]
    exact (hX2 _ h).sub_single μ

/-- The membership of the two end points of a bond agrees at corresponding sites. -/
theorem edge_iff {X₁ : Finset (Torus d ℓ₁)} {X₂ : Finset (Torus d ℓ₂)}
    (hX2₁ : ∀ x ∈ X₁, InBoxK 2 ℓ₁ ℓ₂ cc (liftNear cc x))
    (hX2₂ : ∀ x ∈ X₂, InBoxK 2 ℓ₁ ℓ₂ cc (liftNear cc x)) {x₁ : Torus d ℓ₁} {x₂ : Torus d ℓ₂}
    (hp : PtCorr cc x₁ x₂) {μ : Fin d}
    (hx : x₁ ∈ X₁ ∨ x₁ + Pi.single μ 1 ∈ X₁ ∨ x₂ ∈ X₂ ∨ x₂ + Pi.single μ 1 ∈ X₂) :
    PtCorr cc (x₁ + Pi.single μ 1) (x₂ + Pi.single μ 1) := by
  have hm : InBoxK 1 ℓ₁ ℓ₂ cc (liftNear cc x₁) := by
    rcases hx with h | h | h | h
    · exact margin_edge hX2₁ (Or.inl h) (μ := μ)
    · exact margin_edge hX2₁ (Or.inr h)
    · rw [hp.1]
      exact (margin_edge (ℓ₁ := ℓ₂) (ℓ₂ := ℓ₁) (fun x hx => (hX2₂ x hx).symm) (Or.inl h)
        (μ := μ)).symm
    · rw [hp.1]
      exact (margin_edge (ℓ₁ := ℓ₂) (ℓ₂ := ℓ₁) (fun x hx => (hX2₂ x hx).symm) (Or.inr h)).symm
  exact ptCorr_add_single hp hm μ

end Sites

section Sums

variable {d ℓ₁ ℓ₂ : ℕ} [NeZero ℓ₁] [NeZero ℓ₂] {cc : Fin d → ℤ} {E : Type*}
  [NormedAddCommGroup E] {X₁ : Finset (Torus d ℓ₁)} {X₂ : Finset (Torus d ℓ₂)}
  (hX2₁ : ∀ x ∈ X₁, InBoxK 2 ℓ₁ ℓ₂ cc (liftNear cc x))
  (hX2₂ : ∀ x ∈ X₂, InBoxK 2 ℓ₁ ℓ₂ cc (liftNear cc x))
  (hiff : ∀ x₁ x₂, PtCorr cc x₁ x₂ → (x₁ ∈ X₁ ↔ x₂ ∈ X₂))
  {φ₁ : Torus d ℓ₁ → E} {φ₂ : Torus d ℓ₂ → E}
  (hφ : ∀ x₁ x₂, PtCorr cc x₁ x₂ → φ₁ x₁ = φ₂ x₂)

include hX2₁ hX2₂ hiff hφ in
/-- `∑_{x ∈ X} ‖φ(x) - h‖²` agrees. -/
theorem sumNorm_corr (h : E) :
    ∑ x ∈ X₁, ‖φ₁ x - h‖ ^ 2 = ∑ x ∈ X₂, ‖φ₂ x - h‖ ^ 2 :=
  sum_sites X₁ X₂ (fun x hx => (hX2₁ x hx).inBox) (fun x hx => (hX2₂ x hx).inBox) hiff _ _
    (fun x₁ x₂ hp _ => by rw [hφ x₁ x₂ hp])

include hX2₁ hX2₂ hiff hφ in
/-- The bond energy `bondE` agrees. -/
theorem bondE_corr : bondE X₁ φ₁ = bondE X₂ φ₂ := by
  classical
  unfold bondE
  refine Finset.sum_congr rfl fun μ _ => ?_
  unfold bondEdir
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine sum_sites (cc := cc) _ _ ?_ ?_ ?_ _ _ ?_
  · intro x hx
    exact (hX2₁ x (Finset.mem_filter.1 hx).2.1).inBox
  · intro x hx
    exact (hX2₂ x (Finset.mem_filter.1 hx).2.1).inBox
  · intro x₁ x₂ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      have hpe := edge_iff hX2₁ hX2₂ hp (μ := μ) (Or.inl h1)
      exact ⟨(hiff _ _ hp).1 h1, (hiff _ _ hpe).1 h2⟩
    · rintro ⟨h1, h2⟩
      have hpe := edge_iff hX2₁ hX2₂ hp (μ := μ) (Or.inr (Or.inr (Or.inl h1)))
      exact ⟨(hiff _ _ hp).2 h1, (hiff _ _ hpe).2 h2⟩
  · intro x₁ x₂ hp hx
    have hpe := edge_iff hX2₁ hX2₂ hp (μ := μ) (Or.inl (Finset.mem_filter.1 hx).2.1)
    unfold bondTerm
    rw [hφ _ _ hpe, hφ _ _ hp]

include hX2₁ hX2₂ hiff hφ in
/-- The boundary bond energy `starBondE` agrees. -/
theorem starBondE_corr : starBondE X₁ φ₁ = starBondE X₂ φ₂ := by
  classical
  unfold starBondE
  refine Finset.sum_congr rfl fun μ _ => ?_
  have e : ∀ {ℓ : ℕ} [NeZero ℓ] (X : Finset (Torus d ℓ)) (φ : Torus d ℓ → E),
      (∑ x : Torus d ℓ, if (x ∈ X) ≠ (x + Pi.single μ 1 ∈ X) then bondTerm φ μ x else 0) =
        ∑ x ∈ Finset.univ.filter (fun x : Torus d ℓ => ¬ (x ∈ X ↔ x + Pi.single μ 1 ∈ X)),
          bondTerm φ μ x := by
    intro ℓ _ X φ
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [ne_eq, eq_iff_iff]
  rw [e X₁ φ₁, e X₂ φ₂]
  have key : ∀ x₁ x₂, PtCorr cc x₁ x₂ → (x₁ ∈ X₁ ∨ x₁ + Pi.single μ 1 ∈ X₁ ∨ x₂ ∈ X₂ ∨
      x₂ + Pi.single μ 1 ∈ X₂) → ((x₁ ∈ X₁ ↔ x₁ + Pi.single μ 1 ∈ X₁) ↔
        (x₂ ∈ X₂ ↔ x₂ + Pi.single μ 1 ∈ X₂)) := by
    intro x₁ x₂ hp hx
    have hpe := edge_iff hX2₁ hX2₂ hp (μ := μ) hx
    rw [hiff _ _ hp, hiff _ _ hpe]
  have disj : ∀ {ℓ : ℕ} [NeZero ℓ] (X : Finset (Torus d ℓ)) (x : Torus d ℓ),
      ¬ (x ∈ X ↔ x + Pi.single μ 1 ∈ X) → x ∈ X ∨ x + Pi.single μ 1 ∈ X := by
    intro ℓ _ X x h
    by_contra hc
    have hc' := not_or.1 hc
    exact h ⟨fun h' => absurd h' hc'.1, fun h' => absurd h' hc'.2⟩
  refine sum_sites (cc := cc) _ _ ?_ ?_ ?_ _ _ ?_
  · intro x hx
    exact (margin_edge hX2₁ (disj X₁ x (Finset.mem_filter.1 hx).2) (μ := μ)).inBox
  · intro x hx
    have := (margin_edge (ℓ₁ := ℓ₂) (ℓ₂ := ℓ₁) (fun y hy => (hX2₂ y hy).symm)
      (disj X₂ x (Finset.mem_filter.1 hx).2) (μ := μ))
    exact this.symm.inBox
  · intro x₁ x₂ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have := key x₁ x₂ hp ((disj X₁ x₁ h).elim Or.inl fun h' => Or.inr (Or.inl h'))
      exact fun h' => h (this.2 h')
    · intro h
      have := key x₁ x₂ hp (Or.inr (Or.inr ((disj X₂ x₂ h).elim Or.inl fun h' => Or.inr h')))
      exact fun h' => h (this.1 h')
  · intro x₁ x₂ hp hx
    have hpe := edge_iff hX2₁ hX2₂ hp (μ := μ)
      ((disj X₁ x₁ (Finset.mem_filter.1 hx).2).elim Or.inl fun h' => Or.inr (Or.inl h'))
    unfold bondTerm
    rw [hφ _ _ hpe, hφ _ _ hp]

end Sums

section BlockSums

variable {d ℓ₁ ℓ₂ P q₁ q₂ : ℕ} [NeZero ℓ₁] [NeZero ℓ₂] [NeZero q₁] [NeZero q₂] {cc : Fin d → ℤ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NeZero q₁] [NeZero q₂] in
/-- Sites of corresponding blocks: membership in the block agrees at corresponding sites. -/
theorem fibre_iff (hP : 0 < P) (hℓ₁ : ℓ₁ = P * q₁) (hℓ₂ : ℓ₂ = P * q₂) (hq₁ : 4 ≤ q₁)
    (hq₂ : 4 ≤ q₂) {y₁ : Torus d q₁} {y₂ : Torus d q₂}
    (hy : CCorr cc ℓ₁ ℓ₂ P q₁ q₂ y₁ y₂) {x₁ : Torus d ℓ₁} {x₂ : Torus d ℓ₂}
    (hp : PtCorr cc x₁ x₂) : blockMap P q₁ x₁ = y₁ ↔ blockMap P q₂ x₂ = y₂ := by
  obtain ⟨w, hw, rfl, rfl⟩ := hy
  obtain ⟨v, hv, rfl, rfl⟩ := ptCorr_iff_exists.1 hp
  rw [blockMap_zcast hℓ₁ hP, blockMap_zcast hℓ₂ hP]
  have h1 : zcast q₁ (bidx P v) = zcast q₁ (bidx P w) ↔ bidx P v = bidx P w :=
    ⟨fun h => bidx_eq_of_zcast hP hℓ₁ hq₁ (fun μ => (hw μ).1)
      (fun μ => (inBox_two_mul_le hv μ).1) h.symm |>.symm, fun h => by rw [h]⟩
  have h2 : zcast q₂ (bidx P v) = zcast q₂ (bidx P w) ↔ bidx P v = bidx P w :=
    ⟨fun h => bidx_eq_of_zcast hP hℓ₂ hq₂ (fun μ => (hw μ).2)
      (fun μ => (inBox_two_mul_le hv μ).2) h.symm |>.symm, fun h => by rw [h]⟩
  exact h1.trans h2.symm

omit [NeZero q₁] [NeZero q₂] in
/-- **The block average of corresponding blocks agrees.** -/
theorem bavg_corr (hP : 0 < P) (hℓ₁ : ℓ₁ = P * q₁) (hℓ₂ : ℓ₂ = P * q₂) (hq₁ : 4 ≤ q₁)
    (hq₂ : 4 ≤ q₂) {y₁ : Torus d q₁} {y₂ : Torus d q₂}
    (hy : CCorr cc ℓ₁ ℓ₂ P q₁ q₂ y₁ y₂) {x₀ : Torus d ℓ₁}
    (hx₀ : InBoxK (P + 1) ℓ₁ ℓ₂ cc (liftNear cc x₀)) (hx₀y : blockMap P q₁ x₀ = y₁)
    {φ₁ : Torus d ℓ₁ → E} {φ₂ : Torus d ℓ₂ → E}
    (hφ : ∀ x₁ x₂, PtCorr cc x₁ x₂ → φ₁ x₁ = φ₂ x₂) : bavg P q₁ φ₁ y₁ = bavg P q₂ φ₂ y₂ := by
  classical
  unfold bavg
  congr 1
  have hp₀ := ptCorr_transp (m₂ := ℓ₂) hx₀.inBox
  have hy₂ : blockMap P q₂ (transp ℓ₂ cc x₀) = y₂ := (fibre_iff hP hℓ₁ hℓ₂ hq₁ hq₂ hy hp₀).1 hx₀y
  refine sum_sites (cc := cc) _ _ ?_ ?_ ?_ _ _ ?_
  · intro x hx
    exact (site_margin_of_block hP hℓ₁ hq₁ hx₀ (by rw [hx₀y]; exact mem_blockFibre.1 hx)).1.inBox
  · intro x hx
    have hx₀' : InBoxK (P + 1) ℓ₂ ℓ₁ cc (liftNear cc (transp ℓ₂ cc x₀)) := by
      have := hp₀.1
      rw [← this]; exact hx₀.symm
    have := (site_margin_of_block hP hℓ₂ hq₂ hx₀' (s := x) (by
      rw [hy₂]; exact mem_blockFibre.1 hx)).1
    exact this.symm.inBox
  · intro x₁ x₂ hp
    rw [mem_blockFibre, mem_blockFibre]
    exact fibre_iff hP hℓ₁ hℓ₂ hq₁ hq₂ hy hp
  · intro x₁ x₂ hp _
    exact hφ x₁ x₂ hp

omit [NeZero q₁] [NeZero q₂] in
/-- **A sum over the blocks meeting corresponding finite sets of sites.** -/
theorem sum_blocks {γ : Type*} [AddCommMonoid γ] (hP : 0 < P) (hℓ₁ : ℓ₁ = P * q₁)
    (hℓ₂ : ℓ₂ = P * q₂) (hq₁ : 4 ≤ q₁) (hq₂ : 4 ≤ q₂) {Λ₁ : Finset (Torus d ℓ₁)}
    {Λ₂ : Finset (Torus d ℓ₂)} (hm₁ : ∀ x ∈ Λ₁, InBoxK (P + 1) ℓ₁ ℓ₂ cc (liftNear cc x))
    (hm₂ : ∀ x ∈ Λ₂, InBoxK (P + 1) ℓ₁ ℓ₂ cc (liftNear cc x))
    (hiff : ∀ x₁ x₂, PtCorr cc x₁ x₂ → (x₁ ∈ Λ₁ ↔ x₂ ∈ Λ₂)) (F₁ : Torus d q₁ → γ)
    (F₂ : Torus d q₂ → γ)
    (hF : ∀ y₁ y₂, CCorr cc ℓ₁ ℓ₂ P q₁ q₂ y₁ y₂ → (∃ x ∈ Λ₁, blockMap P q₁ x = y₁) →
      F₁ y₁ = F₂ y₂) :
    ∑ y ∈ Λ₁.image (blockMap P q₁), F₁ y = ∑ y ∈ Λ₂.image (blockMap P q₂), F₂ y := by
  classical
  refine sum_of_rel _ _ (CCorr cc ℓ₁ ℓ₂ P q₁ q₂) F₁ F₂ ?_ ?_ (fun a b b' h h' =>
    CCorr.right_unique hP hℓ₁ hq₁ h h') (fun a a' b h h' => CCorr.left_unique hP hℓ₂ hq₂ h h')
    (fun a b ha _ h => hF a b h (Finset.mem_image.1 ha |>.imp fun x hx => hx))
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have hp := ptCorr_transp (m₂ := ℓ₂) (hm₁ x hx).inBox
    refine ⟨blockMap P q₂ (transp ℓ₂ cc x), Finset.mem_image.2 ⟨_, (hiff _ _ hp).1 hx, rfl⟩, ?_⟩
    obtain ⟨v, hv, h1, h2⟩ := ptCorr_iff_exists.1 hp
    refine ⟨v, hv, ?_, ?_⟩
    · rw [h1, blockMap_zcast hℓ₁ hP]; rfl
    · rw [h2, blockMap_zcast hℓ₂ hP]; rfl
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have hp := ptCorr_transp (m₁ := ℓ₂) (m₂ := ℓ₁) (hm₂ x hx).symm.inBox
    refine ⟨blockMap P q₁ (transp ℓ₁ cc x), Finset.mem_image.2 ⟨_, (hiff _ _ (ptCorr_symm hp)).2 hx,
      rfl⟩, ?_⟩
    obtain ⟨v, hv, h1, h2⟩ := ptCorr_iff_exists.1 (ptCorr_symm hp)
    refine ⟨v, hv, ?_, ?_⟩
    · rw [h1, blockMap_zcast hℓ₁ hP]; rfl
    · rw [h2, blockMap_zcast hℓ₂ hP]; rfl

end BlockSums

end Balaban.RootFSpine
