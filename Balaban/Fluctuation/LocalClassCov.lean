/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassExtend
public import Balaban.Fluctuation.LocalClassChart
public import Balaban.SmallField.Def6AvgInv

/-!
# The local terms on all pairs of fields: a covariant extension (group average)

**What the clauses ask.**  In `SFTermClauses` (`SmallField/Def6v2.lean`):
* `eucE` compares `E_j(r y, r X)(r Ψ, r h)` with `E_j(y, X)(Ψ, h)` for `r` in the paving group
  `pavingSymGroup L m₀ j` at pairs `(Ψ, h)` of the domain of `𝔹_j(X)` whose image lies in the domain
  of `𝔹_j(r X)`: **on the domains only**.  The extension `T ∘ cpl` of `LocalClassExtend.lean` equals
  the recomputed term `T` there, so `eucE` is the lattice covariance of `T` on the domain.
* `eucEloc` compares the **sums** `Eloc_j(y) = Σ_{X ∋ y} E_j(y, X)` at the pairs of the domain of the
  whole-lattice generating set `levelGS j`, for `r` in the full level-`j` group `fullJSymGroup L j`.
  These pairs need not lie in the domain of `𝔹_j(X)` (only with the radius loss of
  `localB_xiDom_of_ambient_xiDom`), so the values of the extension off its domain enter, and they
  must be covariant.  Moreover `fullJSymGroup` does not preserve the paving, so `r X` need not be a
  polymer and `eucEloc` is not a termwise statement at all (CLASS-RULINGS Q-A: it is the density
  covariance (H.3-E), to be obtained at the assembly, e.g. by the Reynolds average over
  `fullJSymGroup / pavingSymGroup` with a relabelling of the translated supports).

**The covariant extension.**  The completion of `LocalClassExtend.lean` is an arbitrary choice off
the domain.  Averaging over a finite group `H` of torus permutations repairs this without any
choice: for a family of functions `f Y` of pairs of fields indexed by sets `Y`, the average
`A Y p = |H|⁻¹ Σ_{s ∈ H} f (s⁻¹ Y) (s⁻¹ p)`
* is `H`-covariant for **all** pairs, with no hypothesis (`avgTerm_act`);
* depends only on `p|_Y` if every `f Y` depends only on `p|_Y` (`avgTerm_local`);
* is analytic on a domain family `D` carried into itself by `H` if every `f Y` is analytic on `D Y`
  (`avgTerm_analytic`);
* is bounded on `D Y` by any bound of the `f (s Y)` on `D (s Y)` invariant under `H`
  (`avgTerm_bound`);
* equals `f Y` on `D Y` if `f` is `H`-covariant on the domains (`avgTerm_eq_of_cov`).

Applied to `f Y = T Y ∘ cpl Y` (`xiFieldDom_avg_completion`) and to the generating sets
`𝔹_{k+1}(Y⁺)` of the local class with `H = pavingSymGroup L m₀ (k + 1)`, whose domains are carried
into each other by `H` (`localB_collar_xiDom_act`), this gives `localB_avg_completion`: an
extension of the recomputed local terms to all pairs of fields which satisfies `localE` and the
paving covariance for all pairs, is analytic and bounded on the class domain, and equals the
recomputed term on the class domain as soon as the recomputed terms are covariant there
(the lattice covariance on the domain, `WIDEGEN.md` W811 item 9).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Filter Topology

section Average

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁]

omit [NeZero L] [NeZero N₁] in
/-- The action of permutations on fields is a left action: `(s r)·Ψ = s·(r·Ψ)`. -/
theorem actField_mul_perm (s r : Equiv.Perm (CTorus d L N₁ m₁ K)) (Ψ : Fld d L N₁ m₁ K N) :
    actField (s * r) Ψ = actField s (actField r Ψ) := by
  funext x
  simp [actField, Equiv.Perm.mul_def]

omit [NeZero L] [NeZero N₁] in
/-- `r⁻¹·(r·Ψ) = Ψ`. -/
theorem actField_inv_actField (r : Equiv.Perm (CTorus d L N₁ m₁ K)) (Ψ : Fld d L N₁ m₁ K N) :
    actField r⁻¹ (actField r Ψ) = Ψ := by
  funext x
  simp [actField, Equiv.Perm.inv_def]

/-- The action of a permutation on pairs of fields is analytic (it is linear). -/
theorem analyticAt_actPair (g : Equiv.Perm (CTorus d L N₁ m₁ K))
    (p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) :
    AnalyticAt ℂ (fun q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N =>
      (actField g q.1, actField g q.2)) p := by
  let ℓ : Fld d L N₁ m₁ K N →ₗ[ℂ] Fld d L N₁ m₁ K N := LinearMap.funLeft ℂ (Fin N → ℂ) g.symm
  have h := (LinearMap.toContinuousLinearMap (LinearMap.prodMap ℓ ℓ)).analyticAt p
  convert h using 1
  funext q
  rfl

omit [NeZero L] [NeZero N₁] in
/-- **The group average is covariant for all pairs of fields.**  For a finite group `H` of
permutations of the torus and `A Y p = |H|⁻¹ Σ_{s ∈ H} f (s⁻¹ Y) (s⁻¹ p)`,
`A (r Y) (r p) = A Y p` for every `r ∈ H`, every set `Y` and every pair `p`. -/
theorem avgTerm_act {F : Type*} [AddCommGroup F] [Module ℂ F]
    (H : Subgroup (Equiv.Perm (CTorus d L N₁ m₁ K))) [Fintype H]
    (f A : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → F)
    (hA : ∀ Y p, A Y p = ((Fintype.card H : ℂ))⁻¹ • ∑ s : H,
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2))
    {r : Equiv.Perm (CTorus d L N₁ m₁ K)} (hr : r ∈ H) (Y : Set (CTorus d L N₁ m₁ K))
    (p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) :
    A (r '' Y) (actField r p.1, actField r p.2) = A Y p := by
  rw [hA, hA]
  congr 1
  refine (Fintype.sum_equiv (Equiv.mulLeft (⟨r, hr⟩ : H)) _ _ fun t => ?_).symm
  have ht : ((Equiv.mulLeft (⟨r, hr⟩ : H) t : H) : Equiv.Perm (CTorus d L N₁ m₁ K)) =
      r * (t : Equiv.Perm (CTorus d L N₁ m₁ K)) := rfl
  simp only [ht, mul_inv_rev, actField_mul_perm, actField_inv_actField]
  congr 1
  simp [Set.image_image]

omit [NeZero L] [NeZero N₁] in
/-- **The group average depends only on the restriction to `Y`** if every `f Y` does. -/
theorem avgTerm_local {F : Type*} [AddCommGroup F] [Module ℂ F]
    (H : Subgroup (Equiv.Perm (CTorus d L N₁ m₁ K))) [Fintype H]
    (f A : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → F)
    (hA : ∀ Y p, A Y p = ((Fintype.card H : ℂ))⁻¹ • ∑ s : H,
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2))
    (hloc : ∀ Y (p p' : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N),
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → f Y p = f Y p')
    (Y : Set (CTorus d L N₁ m₁ K)) (p p' : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N)
    (hpp : ∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) : A Y p = A Y p' := by
  rw [hA, hA]
  congr 1
  refine Finset.sum_congr rfl fun s _ => hloc _ _ _ fun z hz => ?_
  obtain ⟨y, hy, rfl⟩ := hz
  simp only [actField, Equiv.Perm.inv_def, Equiv.symm_symm, Equiv.apply_symm_apply]
  exact hpp y hy

/-- **The group average is analytic on a domain family carried into itself by `H`** if every `f Y`
is analytic on `D Y`. -/
theorem avgTerm_analytic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (H : Subgroup (Equiv.Perm (CTorus d L N₁ m₁ K))) [Fintype H]
    (f A : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → F)
    (hA : ∀ Y p, A Y p = ((Fintype.card H : ℂ))⁻¹ • ∑ s : H,
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2))
    (D : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → Prop)
    (hD : ∀ r ∈ H, ∀ Y p, D Y p → D (r '' Y) (actField r p.1, actField r p.2))
    (hf : ∀ Y, AnalyticOnNhd ℂ (f Y) {p | D Y p}) (Y : Set (CTorus d L N₁ m₁ K)) :
    AnalyticOnNhd ℂ (A Y) {p | D Y p} := by
  intro p hp
  have hAf : A Y = fun p => ((Fintype.card H : ℂ))⁻¹ • ∑ s : H,
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2) := funext (hA Y)
  rw [hAf]
  refine AnalyticAt.const_smul ?_
  have hs : ∀ s : H, AnalyticAt ℂ (fun q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N =>
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ q.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ q.2)) p := fun s =>
    AnalyticAt.comp_of_eq (hf _ _ (hD _ (H.inv_mem s.2) Y p hp))
      (analyticAt_actPair _ p) rfl
  have h := Finset.analyticAt_sum (𝕜 := ℂ) (c := p) Finset.univ fun s _ => hs s
  convert h using 1
  funext q
  simp [Finset.sum_apply]

omit [NeZero L] [NeZero N₁] in
/-- **The group average is bounded on `D Y` by an `H`-invariant bound of the terms.** -/
theorem avgTerm_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (H : Subgroup (Equiv.Perm (CTorus d L N₁ m₁ K))) [Fintype H]
    (f A : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → F)
    (hA : ∀ Y p, A Y p = ((Fintype.card H : ℂ))⁻¹ • ∑ s : H,
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2))
    (D : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → Prop)
    (hD : ∀ r ∈ H, ∀ Y p, D Y p → D (r '' Y) (actField r p.1, actField r p.2))
    (b : Set (CTorus d L N₁ m₁ K) → ℝ) (hb : ∀ r ∈ H, ∀ Y, b (r '' Y) = b Y)
    (hf : ∀ Y p, D Y p → ‖f Y p‖ ≤ b Y) (Y : Set (CTorus d L N₁ m₁ K))
    (p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) (hp : D Y p) : ‖A Y p‖ ≤ b Y := by
  have hc : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  rw [hA, norm_smul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ s : H, f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
      (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
        actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2)‖ ≤ Fintype.card H * b Y := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ s : H, ‖f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2)‖ ≤ b Y := fun s => by
      rw [← hb _ (H.inv_mem s.2) Y]
      exact hf _ _ (hD _ (H.inv_mem s.2) Y p hp)
    refine (Finset.sum_le_sum fun s _ => h1 s).trans ?_
    simp
  calc ((Fintype.card H : ℝ))⁻¹ * ‖∑ s : H, f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2)‖
      ≤ ((Fintype.card H : ℝ))⁻¹ * (Fintype.card H * b Y) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hc.le)
    _ = b Y := by field_simp

omit [NeZero L] [NeZero N₁] in
/-- **The group average equals the term on the domains** if the family is `H`-covariant there. -/
theorem avgTerm_eq_of_cov {F : Type*} [AddCommGroup F] [Module ℂ F]
    (H : Subgroup (Equiv.Perm (CTorus d L N₁ m₁ K))) [Fintype H]
    (f A : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → F)
    (hA : ∀ Y p, A Y p = ((Fintype.card H : ℂ))⁻¹ • ∑ s : H,
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2))
    (D : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → Prop)
    (hf : ∀ r ∈ H, ∀ Y p, D Y p → f (r '' Y) (actField r p.1, actField r p.2) = f Y p)
    (Y : Set (CTorus d L N₁ m₁ K)) (p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) (hp : D Y p) :
    A Y p = f Y p := by
  have hc : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hA]
  have h1 : ∀ s : H, f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
      (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
        actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2) = f Y p := fun s =>
    hf _ (H.inv_mem s.2) Y p hp
  rw [Finset.sum_congr rfl fun s _ => h1 s, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

end Average

section Completion

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The covariant extension of a family of terms from the class domains**: completion
(`LocalClassExtend.lean`) followed by the average over a finite group `H` of torus permutations.
For a family of generating sets `G Y` whose class domains `Ξ^c_j(G Y; 1, ε_j)` are carried into each
other by `H` (`hdom`), and terms `T Y` analytic on the domain of `G Y` and depending there only on the
restriction to `Y`, the average `A Y` of `T (s⁻¹ Y) ∘ cpl (s⁻¹ Y) ∘ s⁻¹` over `s ∈ H`
1. takes the same value at two pairs of fields equal on `Y` (all pairs: the clause `localE`);
2. is `H`-covariant for all pairs of fields;
3. is analytic on the domain of `G Y` (the clause `analyticE`);
4. is bounded on the domain of `G Y` by every `H`-invariant bound of the `T Y` on their domains;
5. equals `T Y` on the domain of `G Y` if the `T Y` are `H`-covariant on the domains. -/
theorem xiFieldDom_avg_completion {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {a : ℕ → ℝ} {ν : ℝ} {εseq : ℕ → ℝ} (HB : BgHyp d L K ϱ a ν) (j : ℕ)
    (H : Subgroup (Equiv.Perm (CTorus d L N₁ m₁ K))) [Fintype H]
    (G : Set (CTorus d L N₁ m₁ K) → GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (hdom : ∀ r ∈ H, ∀ Y (p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j (G Y) p.1 p.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j (G (r '' Y)) (actField r p.1)
        (actField r p.2))
    (cpl : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N →
      Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N)
    (hcpl : ∀ Y p, cpl Y p = Classical.epsilon (fun q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N =>
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j (G Y) q.1 q.2 ∧ ∀ z ∈ Y,
        q.1 z = (Classical.choose (exists_layerProj (N := N) (G Y) Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) (G Y) Y) p).2 z))
    (T : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → F)
    (hT : ∀ Y, AnalyticOnNhd ℂ (T Y)
      {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j (G Y) p.1 p.2})
    (hloc : ∀ Y (p p' : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j (G Y) p.1 p.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j (G Y) p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → T Y p = T Y p')
    (A : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → F)
    (hA : ∀ Y p, A Y p = ((Fintype.card H : ℂ))⁻¹ • ∑ s : H,
      T (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
          (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2))) :
    (∀ Y (Ψ Ψ' h h' : Fld d L N₁ m₁ K N), (∀ x ∈ Y, Ψ x = Ψ' x ∧ h x = h' x) →
      A Y (Ψ, h) = A Y (Ψ', h')) ∧
    (∀ r ∈ H, ∀ Y (p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N),
      A (r '' Y) (actField r p.1, actField r p.2) = A Y p) ∧
    (∀ Y, AnalyticOnNhd ℂ (A Y)
      {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j (G Y) p.1 p.2}) ∧
    (∀ b : Set (CTorus d L N₁ m₁ K) → ℝ, (∀ r ∈ H, ∀ Y, b (r '' Y) = b Y) →
      (∀ Y (p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N),
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j (G Y) p.1 p.2 → ‖T Y p‖ ≤ b Y) →
      ∀ Y (p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N),
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j (G Y) p.1 p.2 → ‖A Y p‖ ≤ b Y) ∧
    ((∀ r ∈ H, ∀ Y (p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N),
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j (G Y) p.1 p.2 →
        T (r '' Y) (actField r p.1, actField r p.2) = T Y p) →
      ∀ Y (p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N),
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j (G Y) p.1 p.2 → A Y p = T Y p) := by
  have hE := fun Y => xiFieldDom_completion_extension HB j (G Y) Y (cpl Y) (hcpl Y) (T Y) (hT Y)
    (hloc Y)
  set f : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → F :=
    fun Y p => T Y (cpl Y p) with hfdef
  have hA' : ∀ Y p, A Y p = ((Fintype.card H : ℂ))⁻¹ • ∑ s : H,
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2) := hA
  have hfT : ∀ Y (p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j (G Y) p.1 p.2 → f Y p = T Y p :=
    fun Y p hp => (hE Y).2.1 p hp
  refine ⟨fun Y Ψ Ψ' h h' hY => ?_, fun r hr Y p => avgTerm_act H f A hA' hr Y p,
    avgTerm_analytic H f A hA' _ hdom fun Y => (hE Y).2.2, fun b hb hTb Y p hp => ?_,
    fun hcov Y p hp => ?_⟩
  · exact avgTerm_local H f A hA' (fun Y p p' hpp => (hE Y).1 p.1 p'.1 p.2 p'.2 hpp) Y _ _ hY
  · refine avgTerm_bound H f A hA' _ hdom b hb (fun Y p hp => ?_) Y p hp
    rw [hfT Y p hp]
    exact hTb Y p hp
  · have hcovf : ∀ r ∈ H, ∀ Y (p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N),
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j (G Y) p.1 p.2 →
        f (r '' Y) (actField r p.1, actField r p.2) = f Y p := fun r hr Y p hp => by
      rw [hfT _ _ (hdom r hr Y p hp), hfT Y p hp]
      exact hcov r hr Y p hp
    rw [avgTerm_eq_of_cov H f A hA'
      (fun Y (p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) =>
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j (G Y) p.1 p.2) hcovf Y p hp,
      hfT Y p hp]

end Completion

section LocalB

open Balaban.SmallField.GsSpec Balaban.LargeField

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱl : ℝ}

/-- **The class domains of the local generating sets are carried into each other by the paving
group**: for `r ∈ pavingSymGroup L m₀ (k + 1)` and the collars `Y⁺`, `(r Y)⁺` of `Y`, `r Y`,
`(Ψ, h) ∈ Ξ^c_{k+1}(𝔹_{k+1}(Y⁺); 1, ε)` implies `(r Ψ, r h) ∈ Ξ^c_{k+1}(𝔹_{k+1}((r Y)⁺); 1, ε)`
(`localB_collar_pavingGS`, `xiDom_image_pavingSymGroup'`). -/
theorem localB_collar_xiDom_act (hk : k + 1 ≤ k + 1) (hsep : ϱl ≤ minSep L (L ^ m₁)) {m₀ : ℕ}
    {r : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))
    {Y Yp Yp' : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (hYp' : ∀ z, z ∈ Yp' ↔ ∃ x ∈ r '' Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    {a : ℕ → ℝ} {ν ε : ℝ} {Ψ h : Fld d L N₁ m₁ (k + 1) N}
    (hX : XiDom (localB (k + 1) hk Yp hsep) a ν (k + 1) ε Ψ h) :
    XiDom (localB (k + 1) hk Yp' hsep) a ν (k + 1) ε (actField r Ψ) (actField r h) :=
  xiDom_image_pavingSymGroup' (le_refl (k + 1)) (localB_collar_gs_spec hk hsep hYp).2 hr
    (localB_collar_pavingGS hk hsep hr hYp hYp') hX

/-- **The covariant extension of the local terms** (`xiFieldDom_avg_completion` at the generating
sets `𝔹_{k+1}(Y⁺)` of the local class and the paving group `H = pavingSymGroup L m₀ (k + 1)`).  For a
family `T Y` of terms analytic on the class domain `Ξ^c_{k+1}(𝔹_{k+1}(Y⁺); 1, ε_{k+1})` and depending
there only on the restriction to `Y` (for the recomputed local term: `localB_eTermHat_evTerm_xiFieldDom`
and `localB_eTermHat_evTerm_local`), the average `A Y` of the completed terms over `H`
1. satisfies `localE` for all pairs of fields;
2. is covariant under `H` for all pairs of fields: `A (r Y) (r Ψ, r h) = A Y (Ψ, h)`;
3. is analytic on the class domain;
4. is bounded there by every `H`-invariant bound of the `T Y` on their domains;
5. equals `T Y` on the class domain if the `T Y` are `H`-covariant on the class domains. -/
theorem localB_avg_completion {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (hk : k + 1 ≤ k + 1) (hsep : ϱl ≤ minSep L (L ^ m₁)) (m₀ : ℕ)
    [Fintype (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))]
    {a : ℕ → ℝ} {ν : ℝ} {εseq : ℕ → ℝ} (HB : BgHyp d L (k + 1) ϱl a ν)
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ Y z, z ∈ Yp Y ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (cpl : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ Y p, cpl Y p = Classical.epsilon
      (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱl).dom (k + 1)
          (localB (k + 1) hk (Yp Y) hsep) q.1 q.2 ∧ ∀ z ∈ Y,
          q.1 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) hk (Yp Y) hsep) Y) p).1 z ∧
          q.2 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) hk (Yp Y) hsep) Y) p).2 z))
    (T : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → F)
    (hT : ∀ Y, AnalyticOnNhd ℂ (T Y)
      {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱl).dom (k + 1)
        (localB (k + 1) hk (Yp Y) hsep) p.1 p.2})
    (hloc : ∀ Y (p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱl).dom (k + 1)
        (localB (k + 1) hk (Yp Y) hsep) p.1 p.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱl).dom (k + 1)
        (localB (k + 1) hk (Yp Y) hsep) p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → T Y p = T Y p')
    (A : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → F)
    (hA : ∀ Y p, A Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1),
        T (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2))) :
    (∀ Y (Ψ Ψ' h h' : Fld d L N₁ m₁ (k + 1) N), (∀ x ∈ Y, Ψ x = Ψ' x ∧ h x = h' x) →
      A Y (Ψ, h) = A Y (Ψ', h')) ∧
    (∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1),
      ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
        A (r '' Y) (actField r p.1, actField r p.2) = A Y p) ∧
    (∀ Y, AnalyticOnNhd ℂ (A Y)
      {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱl).dom (k + 1)
        (localB (k + 1) hk (Yp Y) hsep) p.1 p.2}) ∧
    (∀ b : Set (CTorus d L N₁ m₁ (k + 1)) → ℝ,
      (∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1),
        ∀ Y, b (r '' Y) = b Y) →
      (∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱl).dom (k + 1)
          (localB (k + 1) hk (Yp Y) hsep) p.1 p.2 → ‖T Y p‖ ≤ b Y) →
      ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱl).dom (k + 1)
          (localB (k + 1) hk (Yp Y) hsep) p.1 p.2 → ‖A Y p‖ ≤ b Y) ∧
    ((∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1),
        ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
          (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱl).dom (k + 1)
            (localB (k + 1) hk (Yp Y) hsep) p.1 p.2 →
          T (r '' Y) (actField r p.1, actField r p.2) = T Y p) →
      ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱl).dom (k + 1)
          (localB (k + 1) hk (Yp Y) hsep) p.1 p.2 → A Y p = T Y p) :=
  xiFieldDom_avg_completion HB (k + 1)
    (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))
    (fun Y => localB (k + 1) hk (Yp Y) hsep)
    (fun _ hr Y _ hp => localB_collar_xiDom_act hk hsep hr (hYp Y) (hYp (_ '' Y)) hp)
    cpl hcpl T hT hloc A hA

end LocalB

end Balaban.Localization
