/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.Mayer

/-!
# Product measures grouped by the fibres of a map

For a map `q : Λ → B` of finite sets (sites to groups of sites), a configuration on the sites is a
configuration on the groups, each group carrying the values at its sites: `qSites` identifies
`∏_b (q⁻¹(b) → W)` with `Λ → W`. The product over the groups of the products over their sites of a
one-site measure `γ` (`qRef`) is the site product measure (`map_qSites_pi`), and a function of the
sites of a set `S` composed with `qSites` depends only on the groups meeting `S`
(`depOn_comp_qSites`). The blocks of the torus (`LargeField/Base/KF0AllGoodGas.lean`, `toSites`,
`blockRef`) are the case `q = blockOf`.
-/

@[expose] public section

open MeasureTheory

namespace Balaban.Polymer

variable {Λ B : Type*} (q : Λ → B)

/-- The sites of the group `b`. -/
abbrev QFibre (b : B) : Type _ := {x : Λ // q x = b}

/-- The configuration space of the group `b`: one value in `W` for each site of `b`. -/
abbrev QSpace (W : Type*) (b : B) : Type _ := QFibre q b → W

variable {q} {W : Type*}

/-- The site configuration of a group configuration. -/
def qSites (q : Λ → B) (Φ : ∀ b, QSpace q W b) : Λ → W := fun x => Φ (q x) ⟨x, rfl⟩

/-- The product reference on the groups: on each group the product of the one-site measure `γ`
over the sites of the group. -/
noncomputable def qRef (q : Λ → B) [Fintype Λ] [DecidableEq B] [MeasurableSpace W]
    (γ : Measure W) :
    ∀ b, Measure (QSpace q W b) :=
  fun _ => Measure.pi fun _ => γ

instance qRef_sigmaFinite [Fintype Λ] [DecidableEq B] [MeasurableSpace W] (γ : Measure W)
    [SigmaFinite γ] (b : B) :
    SigmaFinite (qRef q γ b) :=
  inferInstanceAs (SigmaFinite (Measure.pi fun _ : QFibre q b => γ))

instance qRef_isProbabilityMeasure [Fintype Λ] [DecidableEq B] [MeasurableSpace W] (γ : Measure W)
    [IsProbabilityMeasure γ] (b : B) : IsProbabilityMeasure (qRef q γ b) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : QFibre q b => γ))

theorem measurable_qSites [MeasurableSpace W] : Measurable (qSites (W := W) q) := by
  refine Measurable.of_eval fun x => ?_
  exact (measurable_pi_apply (⟨x, rfl⟩ : QFibre q (q x))).comp (measurable_pi_apply (q x))

/-- The restriction map as a measurable equivalence. -/
def qSitesEquiv (q : Λ → B) [MeasurableSpace W] : (∀ b, QSpace q W b) ≃ᵐ (Λ → W) where
  toFun := qSites q
  invFun ψ := fun _ x => ψ x.1
  left_inv Φ := by
    funext b x
    obtain ⟨x, rfl⟩ := x
    rfl
  right_inv ψ := rfl
  measurable_toFun := measurable_qSites
  measurable_invFun := by
    refine Measurable.of_eval fun b => Measurable.of_eval fun x => ?_
    exact measurable_pi_apply x.1

/-- The image of the group product measure under the restriction map is the site product
measure. -/
theorem map_qSites_pi [Fintype Λ] [Fintype B] [DecidableEq B] [MeasurableSpace W]
    (γ : Measure W) [SigmaFinite γ] :
    (Measure.pi (qRef q γ)).map (qSites q) = Measure.pi fun _ : Λ => γ := by
  symm
  refine Measure.pi_eq fun t ht => ?_
  rw [Measure.map_apply measurable_qSites (MeasurableSet.univ_pi ht)]
  have hpre : qSites q ⁻¹' (Set.pi Set.univ t) = Set.pi Set.univ
      (fun b : B => Set.pi Set.univ (fun x : QFibre q b => t x.1)) := by
    ext Φ
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, qSites]
    constructor
    · intro h b x
      obtain ⟨x, hb⟩ := x
      subst hb
      exact h x
    · intro h x
      exact h _ ⟨x, rfl⟩
  rw [hpre, Measure.pi_pi]
  simp only [qRef, Measure.pi_pi]
  exact Fintype.prod_fiberwise q (fun x => γ (t x))

/-- A function of the sites in `S` composed with the restriction map depends only on the groups
meeting `S`. -/
theorem depOn_comp_qSites [DecidableEq B] {S : Finset Λ} {F : (Λ → W) → ℂ}
    (hF : ∀ ψ ψ' : Λ → W, (∀ x ∈ S, ψ x = ψ' x) → F ψ = F ψ') :
    DepOn (S.image q) (fun Φ : ∀ b, QSpace q W b => F (qSites q Φ)) := by
  intro Φ Φ' h
  refine hF _ _ fun x hx => ?_
  exact congrFun (h _ (Finset.mem_image_of_mem _ hx)) ⟨x, rfl⟩

end Balaban.Polymer
