/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassAssembleE
public import Balaban.Fluctuation.LocalClassLabels
public import Balaban.Fluctuation.LocalClassAssembleM
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The new level of the local successor class with centre labels

Orchestrator decisions D1(a), D5(a) (blocker 6; `notes/phase1/LOCALCLASS-REVIEW.md` §§2, 4): the
level `k + 1` of the successor class holds only the **new contributions**, and its energy terms
are labelled by the **centre** `z` of the block `B_{k+1}(z)` of the per-block density
`ℰ^{(k+1)}(z)` (P4 (2.56)-(2.61), (4.20)-(4.22); Lean `StepObjects.E1loc z`, `E0loc z`): the term
of `(z, Y)` is the `Y`-term of the localization expansion of `ℰ^{(k+1)}(z)`.  The uniform
distribution `|Y ∩ Λ_{k+1}|⁻¹ S(Y)` of W851 (`LocalClassAssembly.lean`) is not covariant under
the full level-`(k + 1)` group (`WIDEGEN.md` NEXT (W851) item 4; LOCALCLASS-REVIEW §4); the
centre labels are.

For per-centre polymer terms `TE z Y` (functions of the pair of fields, depending on the centre only
through its block, `hTEblock`), the class term is the average over the paving group of the completed
terms, the centre being transported with the polymer:

`AE z Y p = |H|⁻¹ Σ_{s ∈ H} TE (s⁻¹ z) (s⁻¹ Y) (cpl (s⁻¹ Y) (s⁻¹ p))`,
`Tm.E (k + 1) y Y = AE y Y` for `y ∈ Y`, `0` otherwise.

* `avgTermC_act`, `avgTermC_block`, `avgTermC_local`, `avgTermC_analytic`, `avgTermC_bound`: the
  group average of a centre-labelled family (the analogues of `avgTerm_*` of `LocalClassCov.lean`);
  `blockBase_perm_eq_of_blockBase_eq`: the paving group permutes the `L^K`-blocks;
* `localClass_termClausesE_centre`: the slices at `j = k + 1` of `gs_spec`, `gsStrong`,
  `pavingGS`, `analyticE`, `rotE` (real matrices), `eucE`, `localE`, `boundE` (no volume factor:
  each centre carries its own terms);
* `localClass_centre_Eloc_eq`: **the per-centre identity** `Eloc_{k+1}(y) = 𝒟(y)` on the domain of
  the whole-lattice generating set `levelGS (k + 1)`, from (i) the expansion identity
  `Σ_{Y ∋ y} TE y Y = 𝒟(y)` there, (ii) the inclusion of that domain in the class domains of the
  polymers (so that the completion `cpl` does not change the values:
  `xiFieldDom_completion_extension`),
  (iii) the covariance of the per-block density `𝒟` under the paving group;
* `localClass_eucEloc_centre`: **the clause `eucEloc` at `j = k + 1` for the full group
  `fullJSymGroup L (k + 1)`**, from the same inputs and the full-group covariance of `𝒟`;
* `localClass_centre_Edens_eq`: the density `Σ_{y ∈ Λ_{k+1}} Eloc_{k+1}(y) = Σ_{z ∈ Λ_{k+1}} 𝒟(z)`
  on that domain (P4 (4.22): the new part of the exponent is the sum of the per-block densities).

Not covered: the identification of `TE` with the expansion of the actual new density (OPEN: the
cluster expansion of the interaction `𝒰` of FLUCTUATION (3.3) on the local generator, whose
`δℰ`-blocks are the per-label objects of W811-W848 inside a Cauchy integral); the inputs (i)-(iii)
for the actual objects (the inclusion (ii) carries the radius loss of
`localB_xiDom_of_ambient_xiDom`; the covariance of `E1loc z`, `E0loc z` under the full group is not
landed).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.LargeField Balaban.Fluctuation
  Finset Matrix

section CentreAverage

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁]

/-- **The paving group permutes the `L^K`-blocks**: sites of one block are mapped into one block. -/
theorem blockBase_perm_eq_of_blockBase_eq {m₀ : ℕ} {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    {z z' : CTorus d L N₁ m₁ K}
    (h : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K z =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K z') :
    blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K (r z) =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K (r z') := by
  have hL : 0 < L ^ K := Nat.pos_of_ne_zero (NeZero.ne _)
  have h1 : r z' ∈ r '' box (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K z) (L ^ K) :=
    ⟨z', by rw [h]; exact mem_box_cbase hL z', rfl⟩
  rw [image_box_blockBase (m₀ := m₀) hr z] at h1
  exact (cbase_eq_of_mem_box pow_dvd_torus (aligned_cbase _) h1).symm

omit [NeZero L] [NeZero N₁] in
/-- **The group average of a centre-labelled family is covariant for all pairs of fields**:
for `A z Y p = |H|⁻¹ Σ_{s ∈ H} f (s⁻¹ z) (s⁻¹ Y) (s⁻¹ p)`, `A (r z) (r Y) (r p) = A z Y p`,
`r ∈ H`. -/
theorem avgTermC_act {F : Type*} [AddCommGroup F] [Module ℂ F]
    (H : Subgroup (Equiv.Perm (CTorus d L N₁ m₁ K))) [Fintype H]
    (f A : CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K) →
      Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → F)
    (hA : ∀ z Y p, A z Y p = ((Fintype.card H : ℂ))⁻¹ • ∑ s : H,
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) z)
        (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2))
    {r : Equiv.Perm (CTorus d L N₁ m₁ K)} (hr : r ∈ H) (z : CTorus d L N₁ m₁ K)
    (Y : Set (CTorus d L N₁ m₁ K)) (p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) :
    A (r z) (r '' Y) (actField r p.1, actField r p.2) = A z Y p := by
  rw [hA, hA]
  congr 1
  refine (Fintype.sum_equiv (Equiv.mulLeft (⟨r, hr⟩ : H)) _ _ fun t => ?_).symm
  have ht : ((Equiv.mulLeft (⟨r, hr⟩ : H) t : H) : Equiv.Perm (CTorus d L N₁ m₁ K)) =
      r * (t : Equiv.Perm (CTorus d L N₁ m₁ K)) := rfl
  simp only [ht, _root_.mul_inv_rev, actField_mul_perm, actField_inv_actField]
  congr 1
  · simp [Equiv.Perm.inv_def]
  · simp [Set.image_image, Equiv.Perm.inv_def]

/-- **The group average depends on the centre only through its block**, if the terms do and
`H` lies in the paving group. -/
theorem avgTermC_block {F : Type*} [AddCommGroup F] [Module ℂ F] {m₀ : ℕ}
    (H : Subgroup (Equiv.Perm (CTorus d L N₁ m₁ K))) [Fintype H]
    (hH : H ≤ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    (f A : CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K) →
      Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → F)
    (hA : ∀ z Y p, A z Y p = ((Fintype.card H : ℂ))⁻¹ • ∑ s : H,
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) z)
        (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2))
    (hf : ∀ w w' Y p, blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K w =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K w' → f w Y p = f w' Y p)
    {z z' : CTorus d L N₁ m₁ K}
    (hz : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K z =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K z')
    (Y : Set (CTorus d L N₁ m₁ K)) (p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) :
    A z Y p = A z' Y p := by
  rw [hA, hA]
  congr 1
  refine Finset.sum_congr rfl fun s _ => hf _ _ _ _ ?_
  exact blockBase_perm_eq_of_blockBase_eq (hH (inv_mem s.2)) hz

omit [NeZero L] [NeZero N₁] in
/-- **The group average depends only on the restriction to `Y`** if every `f z Y` does. -/
theorem avgTermC_local {F : Type*} [AddCommGroup F] [Module ℂ F]
    (H : Subgroup (Equiv.Perm (CTorus d L N₁ m₁ K))) [Fintype H]
    (f A : CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K) →
      Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → F)
    (hA : ∀ z Y p, A z Y p = ((Fintype.card H : ℂ))⁻¹ • ∑ s : H,
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) z)
        (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2))
    (hloc : ∀ z Y (p p' : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N),
      (∀ x ∈ Y, p.1 x = p'.1 x ∧ p.2 x = p'.2 x) → f z Y p = f z Y p')
    (z : CTorus d L N₁ m₁ K) (Y : Set (CTorus d L N₁ m₁ K))
    (p p' : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N)
    (hpp : ∀ x ∈ Y, p.1 x = p'.1 x ∧ p.2 x = p'.2 x) : A z Y p = A z Y p' := by
  rw [hA, hA]
  congr 1
  refine Finset.sum_congr rfl fun s _ => hloc _ _ _ _ fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  simp only [actField, Equiv.Perm.inv_def, Equiv.symm_symm, Equiv.apply_symm_apply]
  exact hpp y hy

/-- **The group average is analytic on a domain family carried into itself by `H`** if every
`f z Y` is analytic on `D Y`. -/
theorem avgTermC_analytic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (H : Subgroup (Equiv.Perm (CTorus d L N₁ m₁ K))) [Fintype H]
    (f A : CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K) →
      Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → F)
    (hA : ∀ z Y p, A z Y p = ((Fintype.card H : ℂ))⁻¹ • ∑ s : H,
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) z)
        (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2))
    (D : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → Prop)
    (hD : ∀ r ∈ H, ∀ Y p, D Y p → D (r '' Y) (actField r p.1, actField r p.2))
    (hf : ∀ z Y, AnalyticOnNhd ℂ (f z Y) {p | D Y p}) (z : CTorus d L N₁ m₁ K)
    (Y : Set (CTorus d L N₁ m₁ K)) : AnalyticOnNhd ℂ (A z Y) {p | D Y p} := by
  intro p hp
  have hAf : A z Y = fun p => ((Fintype.card H : ℂ))⁻¹ • ∑ s : H,
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) z)
        (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2) := funext (hA z Y)
  rw [hAf]
  refine AnalyticAt.const_smul ?_
  have hs : ∀ s : H, AnalyticAt ℂ (fun q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N =>
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) z)
        (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ q.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ q.2)) p := fun s =>
    AnalyticAt.comp_of_eq (hf _ _ _ (hD _ (H.inv_mem s.2) Y p hp))
      (analyticAt_actPair _ p) rfl
  have h := Finset.analyticAt_sum (𝕜 := ℂ) (c := p) Finset.univ fun s _ => hs s
  convert h using 1
  funext q
  simp [Finset.sum_apply]

omit [NeZero L] [NeZero N₁] in
/-- **The group average is bounded on `D Y` by an `H`-invariant bound of the terms of the centres
of `Y`.** -/
theorem avgTermC_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (H : Subgroup (Equiv.Perm (CTorus d L N₁ m₁ K))) [Fintype H]
    (f A : CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K) →
      Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → F)
    (hA : ∀ z Y p, A z Y p = ((Fintype.card H : ℂ))⁻¹ • ∑ s : H,
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) z)
        (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2))
    (D : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → Prop)
    (hD : ∀ r ∈ H, ∀ Y p, D Y p → D (r '' Y) (actField r p.1, actField r p.2))
    (b : Set (CTorus d L N₁ m₁ K) → ℝ) (hb : ∀ r ∈ H, ∀ Y, b (r '' Y) = b Y)
    (hf : ∀ z Y p, z ∈ Y → D Y p → ‖f z Y p‖ ≤ b Y) {z : CTorus d L N₁ m₁ K}
    {Y : Set (CTorus d L N₁ m₁ K)} (hz : z ∈ Y) {p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N}
    (hp : D Y p) : ‖A z Y p‖ ≤ b Y := by
  have hc : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  rw [hA, norm_smul, norm_inv, Complex.norm_natCast]
  have h1 : ∀ s : H, ‖f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ :
      Equiv.Perm (CTorus d L N₁ m₁ K)) z)
        (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2)‖ ≤ b Y := fun s => by
    rw [← hb _ (H.inv_mem s.2) Y]
    exact hf _ _ _ (Set.mem_image_of_mem _ hz) (hD _ (H.inv_mem s.2) Y p hp)
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => h1 s)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  calc ((Fintype.card H : ℝ))⁻¹ * ‖∑ s : H, f (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ :
        Equiv.Perm (CTorus d L N₁ m₁ K)) z)
        (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2)‖
      ≤ ((Fintype.card H : ℝ))⁻¹ * (Fintype.card H * b Y) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hc.le)
    _ = b Y := by field_simp

end CentreAverage

section CentreClass

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

open Classical in
/-- **The E-fields of the new level `k + 1` with centre labels** (D1(a), D5(a)).  Setting as in
`localClass_termClausesE`: index `5 L M₁ = minSep L (L ^ m₁)`, generating sets
`𝔹_{k+1}(Y⁺) = localB (k + 1) … (Yp Y)` (`hgs`), class domain `xiFieldDom a ν εseq`.  Let `TE z Y`
be the term of the centre `z` and the polymer `Y` (in the application: the `Y`-term of the
localization of the per-block new density `ℰ^{(k+1)}(z)`), depending on `z` only through its block
(`hTEblock`), with, for polymers `Y ∈ 𝒟_{k+1}` and on the class domain of `𝔹_{k+1}(Y⁺)`:
* `hTEan`: analyticity; `hTEloc`: dependence on the restriction to `Y` only;
* `hTEbd`: `‖TE z Y‖ ≤ E₀ e^{-κ d_{k+1}(Y)}` for `z ∈ Y`;
* `hTErot`: invariance under real orthogonal `Q`.
Let `AE z Y` be the average over the paving group of the completed terms, the centre transported
with the polymer, and `Tm.E (k + 1) y Y = AE y Y` for `y ∈ Y`.  Then the slices at `j = k + 1` of
`gs_spec`, `gsStrong`, `pavingGS`, `analyticE`, `rotE` (real matrices), `eucE`, `localE`, `boundE`
hold.  No paving covariance of `TE` is used. -/
theorem localClass_termClausesE_centre {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
    [Fintype (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1))]
    {a : ℕ → ℝ} {ν : ℝ} {εseq : ℕ → ℝ}
    (HB : BgHyp d L (k + 1) (minSep L (L ^ m₁)) a ν)
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ Y z, z ∈ Yp Y ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (Tm : Terms d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁)))
    (hgs : ∀ Y, Tm.gs (k + 1) Y =
      localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁))))
    (cpl : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ Y p, cpl Y p = Classical.epsilon
      (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
          (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2 ∧
        ∀ z ∈ Y,
          q.1 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).1 z ∧
          q.2 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).2 z))
    (TE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTEblock : ∀ z z' Y p, blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) z =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) z' → TE z Y p = TE z' Y p)
    (hTEan : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → AnalyticOnNhd ℂ (TE z Y)
      {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2})
    (hTEloc : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ x ∈ Y, p.1 x = p'.1 x ∧ p.2 x = p'.2 x) → TE z Y p = TE z Y p')
    (hTEbd : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → z ∈ Y →
      ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      ‖TE z Y p‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y))
    (hTErot : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      TE z Y (rotField (cmat Q) p.1, rotField (cmat Q) p.2) = TE z Y p)
    (AE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hAE : ∀ z Y p, AE z Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        TE (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) z)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2)))
    (hE : ∀ y Y Ψ h, Tm.E (k + 1) y Y Ψ h = if y ∈ Y then AE y Y (Ψ, h) else 0) :
    -- `gs_spec`
    (∀ X, IsPolyDom P.m₀ (k + 1) X →
      X ⊆ ↑((Tm.gs (k + 1) X).Ω 1) ∧ ∀ i, k + 1 < i → (Tm.gs (k + 1) X).Ω i = ∅) ∧
    -- `gsStrong`
    (∀ X, IsPolyDom P.m₀ (k + 1) X →
      GsSpecStrong (k + 1) (le_refl (k + 1)) X (Tm.gs (k + 1) X)) ∧
    -- `pavingGS`
    (∀ X, IsPolyDom P.m₀ (k + 1) X →
      ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1), ∀ i,
        (((Tm.gs (k + 1) (r '' X)).Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) :
            Set (CTorus d L N₁ m₁ (k + 1))) =
          r '' (((Tm.gs (k + 1) X).Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) :
            Set (CTorus d L N₁ m₁ (k + 1)))) ∧
    -- `analyticE`
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X →
      AnalyticOnNhd ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Tm.E (k + 1) y X p.1 p.2)
        {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
          (Tm.gs (k + 1) X) p.1 p.2}) ∧
    -- `rotE`, real matrices
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X → ∀ R : Matrix (Fin N) (Fin N) ℂ, IsRot R →
      (∀ i j, (R i j).im = 0) → ∀ Ψ h,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) (rotField R Ψ) (rotField R h) →
      Tm.E (k + 1) y X (rotField R Ψ) (rotField R h) = Tm.E (k + 1) y X Ψ h) ∧
    -- `eucE`
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X →
      ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1), ∀ Ψ h,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) (r '' X)) (actField r Ψ) (actField r h) →
      Tm.E (k + 1) (blockBase L (k + 1) (r y)) (r '' X) (actField r Ψ) (actField r h) =
        Tm.E (k + 1) y X Ψ h) ∧
    -- `localE`
    (∀ y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
      Tm.E (k + 1) y X Ψ h = Tm.E (k + 1) y X Ψ' h') ∧
    -- `boundE`
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X → ∀ Ψ h,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      ‖Tm.E (k + 1) y X Ψ h‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) X)) := by
  set G : Set (CTorus d L N₁ m₁ (k + 1)) → GeneratingSet d L (N₁ * L ^ m₁) (k + 1)
    (minSep L (L ^ m₁)) :=
    fun Y => localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁))) with hG
  set D : Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → Prop :=
    fun Y p => (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom
      (k + 1) (G Y) p.1 p.2 with hD
  have hDL : ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N), D Y p →
      p ∈ layerSub (G Y) := fun Y p hp => xiDom_mem_layerSub hp
  have hdom : ∀ r ∈ (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)),
      ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N), D Y p →
      D (r '' Y) (actField r p.1, actField r p.2) := fun r hr Y p hp =>
    localB_collar_xiDom_act (le_refl (k + 1)) (le_refl (minSep L (L ^ m₁))) hr (hYp Y)
      (hYp (r '' Y)) hp
  set f : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ :=
    fun z Y p => TE z Y (cpl Y p) with hf
  have hAE' : ∀ z Y p, AE z Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀
        (k + 1)) : ℂ))⁻¹ •
      ∑ s : (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)),
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) z)
        (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
          Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2) := hAE
  -- the completion facts at a polymer
  have hext : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y →
      (∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N, D Y p → f z Y p = TE z Y p) ∧
      AnalyticOnNhd ℂ (f z Y) {p | D Y p} := fun z Y hY => by
    obtain ⟨-, e2, e3⟩ := xiFieldDom_completion_extension HB (k + 1) (G Y) Y (cpl Y) (hcpl Y)
      (TE z Y) (hTEan z Y hY) (hTEloc z Y hY)
    exact ⟨e2, e3⟩
  have hfloc : ∀ z Y (p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (∀ x ∈ Y, p.1 x = p'.1 x ∧ p.2 x = p'.2 x) → f z Y p = f z Y p' := fun z Y p p' hpp => by
    obtain ⟨c1, -⟩ := fieldDom_completion_spec _ (k + 1) (G Y) Y (cpl Y) (hcpl Y) (hDL Y)
    simp only [hf]
    rw [c1 p.1 p'.1 p.2 p'.2 hpp]
  -- the polymer domain family, carried into itself by the paving group
  set D' : Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → Prop :=
    fun Y p => IsPolyDom P.m₀ (k + 1) Y ∧ D Y p with hD'
  have hdom' : ∀ r ∈ (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)),
      ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N), D' Y p →
      D' (r '' Y) (actField r p.1, actField r p.2) := fun r hr Y p hp =>
    ⟨(isPolyDom_image_iff hN hr Y).2 hp.1, hdom r hr Y p hp.2⟩
  have hfan : ∀ z Y, AnalyticOnNhd ℂ (f z Y) {p | D' Y p} := fun z Y p hp =>
    (hext z Y hp.1).2 p hp.2
  have hAcov : ∀ r ∈ (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)),
      ∀ z Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      AE (r z) (r '' Y) (actField r p.1, actField r p.2) = AE z Y p := fun r hr z Y p =>
    avgTermC_act
      (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) f AE
      hAE' hr z Y p
  have hAblock : ∀ z z' Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) z =
        blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) z' →
      AE z Y p = AE z' Y p := fun z z' Y p hzz =>
    avgTermC_block
      (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) le_rfl f AE
      hAE' (fun w w' Y p hww => by simp only [hf]; exact hTEblock w w' _ _ hww) hzz Y p
  have hAloc := avgTermC_local
    (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) f AE
    hAE' hfloc
  have hAan := avgTermC_analytic
    (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) f AE
    hAE' D' hdom' hfan
  have hAbd : ∀ z Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N), z ∈ Y → D' Y p →
      ‖AE z Y p‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y) := fun z Y p hz hp =>
    avgTermC_bound (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) f AE
      hAE' D' hdom' (fun Y => P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y))
      (boundE_paving_invariant hN P.E₀ P.κ)
      (fun z Y p hz hp => by rw [(hext z Y hp.1).1 p hp.2]; exact hTEbd z Y hp.1 hz p hp.2) hz hp
  refine ⟨fun X _ => ?_, fun X _ => ?_, fun X _ r hr i => ?_, fun y X hX hy => ?_,
    fun y X hX hy R hR hre Ψ h h1 h2 => ?_, fun y X hX hy r hr Ψ h _ _ => ?_,
    fun y X Ψ Ψ' h h' hX => ?_, fun y X hX hy Ψ h h1 => ?_⟩
  · rw [hgs]
    exact localB_collar_gs_spec (le_refl (k + 1)) (le_refl (minSep L (L ^ m₁))) (hYp X)
  · rw [hgs]
    exact localB_collar_gsSpecStrong_of_subset (le_refl (k + 1)) (le_refl (minSep L (L ^ m₁)))
      (hYp X)
  · rw [hgs, hgs]
    exact localB_collar_pavingGS (le_refl (k + 1)) (le_refl (minSep L (L ^ m₁))) hr (hYp X)
      (hYp (r '' X)) i
  · have hEf : (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        Tm.E (k + 1) y X p.1 p.2) = fun p => AE y X p := by
      funext p
      rw [hE]
      simp [hy]
    rw [hEf, hgs]
    intro p hp
    exact hAan y X p ⟨hX, hp⟩
  · obtain ⟨Q, hQ, rfl⟩ := exists_cmat_of_isRot_real hR hre
    rw [hE, hE]
    simp only [hy, ↓reduceIte]
    rw [hgs] at h1 h2
    rw [hAE', hAE']
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    have hs : ((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹) ∈
        (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) := inv_mem s.2
    have hY' : IsPolyDom P.m₀ (k + 1)
        (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))
          '' X) := (isPolyDom_image_iff hN hs X).2 hX
    have hp1 := hdom _ hs X (Ψ, h) h1
    have hp2 := hdom _ hs X (rotField (cmat Q) Ψ, rotField (cmat Q) h) h2
    simp only at hp1 hp2
    rw [actField_rotField, actField_rotField] at hp2 ⊢
    rw [(hext _ _ hY').1 _ hp2, (hext _ _ hY').1 _ hp1]
    exact hTErot _ _ hY' Q hQ _ hp1
  · have hmem := blockBase_mem_image hr (blockUnion_of_isPolyDom hN hX) hy
    rw [hE, hE]
    simp only [hmem, hy, ↓reduceIte]
    rw [hAblock _ (r y) _ _ (cbase_eq_self_of_aligned (aligned_cbase _))]
    exact hAcov r hr y X (Ψ, h)
  · rw [hE, hE, hAloc y X (Ψ, h) (Ψ', h') hX]
  · rw [hE]
    simp only [hy, ↓reduceIte]
    rw [hgs] at h1
    exact hAbd y X (Ψ, h) hy ⟨hX, h1⟩

/-- **The domain of the whole-lattice generating set of level `k + 1` is invariant under the
paving group** (`xiDom_image_pavingSymGroup'` with `𝔹 = 𝔹' = levelGS (k + 1)`). -/
theorem xiFieldDom_levelGS_act {m₀ : ℕ} {a : ℕ → ℝ} {ν : ℝ} {εseq : ℕ → ℝ} {ϱ : ℝ}
    {r : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))
    {q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hq : (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
      (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1))) q.1 q.2) :
    (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
      (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
      (actField r q.1) (actField r q.2) := by
  refine xiDom_image_pavingSymGroup' (k := k + 1) (j := k + 1) (m₀ := m₀) le_rfl
    (fun i hi => ?_) hr (fun i => ?_) hq
  · simp [levelGS, Nat.not_le.2 hi]
  · by_cases hi : i ≤ k + 1
    · simp [levelGS, hi, Set.image_univ_of_surjective r.surjective]
    · simp [levelGS, hi]

open Classical in
/-- **The per-centre identity** (LOCALCLASS-REVIEW §4 (ii)): for the centre-labelled class terms
of `localClass_termClausesE_centre`, at every pair `p` of the domain of the whole-lattice
generating set `levelGS (k + 1)`, `Eloc_{k+1}(y)(p) = 𝒟(y)(p)`, where `𝒟` is the per-block
density.  Inputs, on that domain:
* `hchart`: it lies in the class domain of every polymer (so the completion `cpl` does not change
  the values of the terms there, `xiFieldDom_completion_extension`);
* `hDz`: the localization expansion of the density, `Σ_{Y ∋ y} TE y Y = 𝒟(y)`;
* `hDzcov`: the covariance of the density under the paving group. -/
theorem localClass_centre_Eloc_eq {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
    [Fintype (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1))]
    {a : ℕ → ℝ} {ν : ℝ} {εseq : ℕ → ℝ}
    (HB : BgHyp d L (k + 1) (minSep L (L ^ m₁)) a ν)
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁ m₁ (k + 1)))
    (Tm : Terms d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁)))
    (cpl : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ Y p, cpl Y p = Classical.epsilon
      (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
          (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2 ∧
        ∀ z ∈ Y,
          q.1 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).1 z ∧
          q.2 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).2 z))
    (TE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTEan : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → AnalyticOnNhd ℂ (TE z Y)
      {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2})
    (hTEloc : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ x ∈ Y, p.1 x = p'.1 x ∧ p.2 x = p'.2 x) → TE z Y p = TE z Y p')
    (AE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hAE : ∀ z Y p, AE z Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        TE (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) z)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2)))
    (hE : ∀ y Y Ψ h, Tm.E (k + 1) y Y Ψ h = if y ∈ Y then AE y Y (Ψ, h) else 0)
    (hchart : ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2)
    (Dz : CTorus d L N₁ m₁ (k + 1) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hDz : ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      ∑ᶠ Y ∈ polysAt P.m₀ (k + 1) y, TE y Y q = Dz y q)
    (hDzcov : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      Dz (r y) (actField r q.1, actField r q.2) = Dz y q)
    (y : CTorus d L N₁ m₁ (k + 1)) {p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hp : (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
      (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
      p.1 p.2) :
    Eloc P.m₀ Tm (k + 1) y p.1 p.2 = Dz y p := by
  have hinv : ∀ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹) ∈
        pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1) :=
    fun s => inv_mem s.2
  have hfin : (polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) P.m₀ (k + 1) y).Finite :=
    Set.toFinite _
  -- the class terms at the polymers of `y`, completion removed
  have hterm : ∀ Y ∈ polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) P.m₀ (k + 1) y,
      Tm.E (k + 1) y Y p.1 p.2 =
        ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀
          (k + 1)) : ℂ))⁻¹ •
        ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
          TE (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) y)
            (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2) := by
    intro Y hY
    rw [hE]
    simp only [hY.2, ↓reduceIte]
    rw [hAE]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    have hY' : IsPolyDom P.m₀ (k + 1)
        (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))
          '' Y) := (isPolyDom_image_iff hN (hinv s) Y).2 hY.1
    have hq := xiFieldDom_levelGS_act (hinv s) hp
    exact (xiFieldDom_completion_extension HB (k + 1) _ _ _ (hcpl _) _ (hTEan _ _ hY')
      (hTEloc _ _ hY')).2.1 _ (hchart _ hY' _ hq)
  -- the inner sums, one element of the group at a time
  have hinner : ∀ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∑ Y ∈ hfin.toFinset,
        TE (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) y)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2) = Dz y p := by
    intro s
    set t : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)) := (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹
      with ht
    have hts : t ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1) :=
      hinv s
    have hti : t⁻¹ ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1) :=
      inv_mem hts
    have hq := xiFieldDom_levelGS_act hts hp
    rw [← finsum_mem_eq_finite_toFinset_sum _ hfin]
    rw [finsum_mem_eq_of_bijOn (t := polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) P.m₀
        (k + 1) (t y)) (g := fun Y' => TE (t y) Y' (actField t p.1, actField t p.2))
      (fun Y => t '' Y) ⟨fun Y hY => ?_, fun Y _ Y' _ hYY => ?_, fun Y' hY' => ?_⟩
      fun Y _ => rfl]
    · rw [hDz _ _ hq]
      exact hDzcov t hts y p hp hq
    · exact ⟨(isPolyDom_image_iff hN hts Y).2 hY.1, Set.mem_image_of_mem _ hY.2⟩
    · exact Set.image_injective.2 t.injective hYY
    · refine ⟨(⇑(t⁻¹)) '' Y', ⟨(isPolyDom_image_iff hN hti Y').2 hY'.1, ?_⟩, ?_⟩
      · exact ⟨t y, hY'.2, by simp [Equiv.Perm.inv_def]⟩
      · simp only
        rw [Set.image_image]
        simp [Equiv.Perm.inv_def]
  have hc : (Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀
      (k + 1)) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold Eloc
  rw [finsum_mem_congr rfl hterm, finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.smul_sum,
    Finset.sum_comm]
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hc, one_mul]

open Classical in
/-- **The clause `eucEloc` at `j = k + 1` for the full group `fullJSymGroup L (k + 1)`**
(D5(a); P4 (H.3), (2.56)-(2.61): the per-block density is covariant under every Euclidean symmetry
of the level-`(k + 1)` lattice).  For the centre-labelled class terms of
`localClass_termClausesE_centre`, from the per-centre identity `localClass_centre_Eloc_eq` (inputs
`hchart`, `hDz`) and the covariance of the per-block density `𝒟` under the full group (`hDzfull`),
`𝒟` depending on the centre only through its block (`hDzblock`). -/
theorem localClass_eucEloc_centre {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
    [Fintype (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1))]
    {a : ℕ → ℝ} {ν : ℝ} {εseq : ℕ → ℝ}
    (HB : BgHyp d L (k + 1) (minSep L (L ^ m₁)) a ν)
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁ m₁ (k + 1)))
    (Tm : Terms d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁)))
    (cpl : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ Y p, cpl Y p = Classical.epsilon
      (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
          (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2 ∧
        ∀ z ∈ Y,
          q.1 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).1 z ∧
          q.2 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).2 z))
    (TE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTEan : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → AnalyticOnNhd ℂ (TE z Y)
      {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2})
    (hTEloc : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ x ∈ Y, p.1 x = p'.1 x ∧ p.2 x = p'.2 x) → TE z Y p = TE z Y p')
    (AE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hAE : ∀ z Y p, AE z Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        TE (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) z)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2)))
    (hE : ∀ y Y Ψ h, Tm.E (k + 1) y Y Ψ h = if y ∈ Y then AE y Y (Ψ, h) else 0)
    (hchart : ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2)
    (Dz : CTorus d L N₁ m₁ (k + 1) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hDz : ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      ∑ᶠ Y ∈ polysAt P.m₀ (k + 1) y, TE y Y q = Dz y q)
    (hDzblock : ∀ y y' q, blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) y =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) y' → Dz y q = Dz y' q)
    (hDzfull : ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1),
      ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      Dz (r y) (actField r q.1, actField r q.2) = Dz y q) :
    ∀ hjk : k + 1 ≤ k + 1, ∀ y,
      ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1), ∀ Ψ h,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) hjk) Ψ h →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) hjk)
        (actField r Ψ) (actField r h) →
      Eloc P.m₀ Tm (k + 1) (blockBase L (k + 1) (r y)) (actField r Ψ) (actField r h) =
        Eloc P.m₀ Tm (k + 1) y Ψ h := by
  intro _ y r hr Ψ h h1 h2
  have hle : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1) ≤
      fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) :=
    symGroupBy_le_of_dvd pow_dvd_cellSide (cellSide_pos (L := L) P.m₀ m₁ (k + 1))
  have hcov : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      Dz (r y) (actField r q.1, actField r q.2) = Dz y q := fun r hr' => hDzfull r (hle hr')
  have e1 := localClass_centre_Eloc_eq hN HB Yp Tm cpl hcpl TE hTEan hTEloc AE hAE hE hchart Dz
    hDz hcov (blockBase L (k + 1) (r y)) (p := (actField r Ψ, actField r h)) h2
  have e2 := localClass_centre_Eloc_eq hN HB Yp Tm cpl hcpl TE hTEan hTEloc AE hAE hE hchart Dz
    hDz hcov y (p := (Ψ, h)) h1
  simp only at e1 e2
  rw [e1, e2, hDzblock _ (r y) _ (cbase_eq_self_of_aligned (aligned_cbase _))]
  exact hDzfull r hr y (Ψ, h) h1 h2

open Classical in
/-- **The density of the new level is the sum of the per-block densities** (P4 (4.22)): for the
centre-labelled class terms, at every pair of the domain of `levelGS (k + 1)`,
`ℰ^{(k+1)} = Σ_{y ∈ Λ_{k+1}} Eloc_{k+1}(y) = Σ_{z ∈ Λ_{k+1}} 𝒟(z)` (inputs of
`localClass_centre_Eloc_eq`). -/
theorem localClass_centre_Edens_eq {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
    [Fintype (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1))]
    {a : ℕ → ℝ} {ν : ℝ} {εseq : ℕ → ℝ}
    (HB : BgHyp d L (k + 1) (minSep L (L ^ m₁)) a ν)
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁ m₁ (k + 1)))
    (Tm : Terms d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁)))
    (cpl : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ Y p, cpl Y p = Classical.epsilon
      (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
          (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2 ∧
        ∀ z ∈ Y,
          q.1 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).1 z ∧
          q.2 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).2 z))
    (TE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTEan : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → AnalyticOnNhd ℂ (TE z Y)
      {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2})
    (hTEloc : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ x ∈ Y, p.1 x = p'.1 x ∧ p.2 x = p'.2 x) → TE z Y p = TE z Y p')
    (AE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hAE : ∀ z Y p, AE z Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        TE (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) z)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2)))
    (hE : ∀ y Y Ψ h, Tm.E (k + 1) y Y Ψ h = if y ∈ Y then AE y Y (Ψ, h) else 0)
    (hchart : ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2)
    (Dz : CTorus d L N₁ m₁ (k + 1) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hDz : ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      ∑ᶠ Y ∈ polysAt P.m₀ (k + 1) y, TE y Y q = Dz y q)
    (hDzcov : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      Dz (r y) (actField r q.1, actField r q.2) = Dz y q)
    {p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hp : (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
      (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
      p.1 p.2) :
    Edens P.m₀ Tm (k + 1) p.1 p.2 =
      ∑ z ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))).filter (Aligned (L ^ (k + 1))),
        Dz z p := by
  unfold Edens
  exact Finset.sum_congr rfl fun z _ => localClass_centre_Eloc_eq hN HB Yp Tm cpl hcpl TE hTEan
    hTEloc AE hAE hE hchart Dz hDz hDzcov z hp

/-! ### The source terms: the per-site identity and `eucMloc` for the full group

The source terms of the new level are already labelled by sites (`localClass_termClausesM`); the
counterexample of `WIDEGEN.md` NEXT (W851) item 4 does not apply to them, and only the per-site
identity with the per-site density `𝒟_M(x)` (P4 (4.18): `ℳ^{(k+1)}(x)`) remains
(LOCALCLASS-REVIEW §4 (iv)). -/

open Classical in
/-- **The per-site identity of the source terms**: for the averaged, completed source terms of
`localClass_termClausesM`, at every pair `p` of the domain of `levelGS (k + 1)` and every source,
`Mloc_{k+1}(x)(p, g) = 𝒟_M(x)(p, g)`, from the inclusion `hchart` of that domain in the class
domains of the polymers, the localization expansion `hDM` of `𝒟_M` there and the covariance
`hDMcov` of `𝒟_M` under the paving group. -/
theorem localClass_site_Mloc_eq {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
    [Fintype (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1))]
    {a : ℕ → ℝ} {ν : ℝ} {εseq : ℕ → ℝ}
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁ m₁ (k + 1)))
    (Tm : Terms d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁)))
    (cpl : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ Y p, cpl Y p = Classical.epsilon
      (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
          (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2 ∧
        ∀ z ∈ Y,
          q.1 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).1 z ∧
          q.2 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).2 z))
    (TM : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hTMloc : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → ∀ g, TM x Y (p, g) = TM x Y (p', g))
    (AM : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hAM : ∀ x Y q, AM x Y q =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        TM (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.2),
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.2))
    (hM : ∀ x Y Ψ h g, Tm.M (k + 1) x Y Ψ h g = AM x Y ((Ψ, h), g))
    (hchart : ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2)
    (DM : CTorus d L N₁ m₁ (k + 1) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hDM : ∀ x (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      ∑ᶠ Y ∈ polysAt P.m₀ (k + 1) x, TM x Y (q, g) = DM x (q, g))
    (hDMcov : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∀ x (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      DM (r x) ((actField r q.1, actField r q.2), actField r g) = DM x (q, g))
    (x : CTorus d L N₁ m₁ (k + 1)) {p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hp : (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
      (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
      p.1 p.2) (g : Fld d L N₁ m₁ (k + 1) N) :
    Mloc P.m₀ Tm (k + 1) x p.1 p.2 g = DM x (p, g) := by
  have hinv : ∀ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹) ∈
        pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1) :=
    fun s => inv_mem s.2
  have hfin : (polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) P.m₀ (k + 1) x).Finite :=
    Set.toFinite _
  have hterm : ∀ Y ∈ polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) P.m₀ (k + 1) x,
      Tm.M (k + 1) x Y p.1 p.2 g =
        ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀
          (k + 1)) : ℂ))⁻¹ •
        ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
          TM (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
            (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            ((actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
                actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2),
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ g) := by
    intro Y hY
    rw [hM, hAM]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    have hY' : IsPolyDom P.m₀ (k + 1)
        (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))
          '' Y) := (isPolyDom_image_iff hN (hinv s) Y).2 hY.1
    have hq := hchart _ hY' (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
      actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2)
      (xiFieldDom_levelGS_act (hinv s) hp)
    obtain ⟨-, c2⟩ := fieldDom_completion_spec _ (k + 1) _ _ _ (hcpl _)
      (fun q hq => xiDom_mem_layerSub hq)
    exact hTMloc _ _ hY' _ _ (c2 _ hq).1 hq (c2 _ hq).2 _
  have hinner : ∀ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∑ Y ∈ hfin.toFinset,
        TM (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          ((actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2),
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ g) = DM x (p, g) := by
    intro s
    set t : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)) := (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹
      with ht
    have hts : t ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1) :=
      hinv s
    have hti : t⁻¹ ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1) :=
      inv_mem hts
    have hq := xiFieldDom_levelGS_act hts hp
    rw [← finsum_mem_eq_finite_toFinset_sum _ hfin]
    rw [finsum_mem_eq_of_bijOn (t := polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) P.m₀
        (k + 1) (t x)) (g := fun Y' => TM (t x) Y' ((actField t p.1, actField t p.2), actField t g))
      (fun Y => t '' Y) ⟨fun Y hY => ?_, fun Y _ Y' _ hYY => ?_, fun Y' hY' => ?_⟩
      fun Y _ => rfl]
    · rw [hDM _ _ _ hq]
      exact hDMcov t hts x p g hp hq
    · exact ⟨(isPolyDom_image_iff hN hts Y).2 hY.1, Set.mem_image_of_mem _ hY.2⟩
    · exact Set.image_injective.2 t.injective hYY
    · refine ⟨(⇑(t⁻¹)) '' Y', ⟨(isPolyDom_image_iff hN hti Y').2 hY'.1, ?_⟩, ?_⟩
      · exact ⟨t x, hY'.2, by simp [Equiv.Perm.inv_def]⟩
      · simp only
        rw [Set.image_image]
        simp [Equiv.Perm.inv_def]
  have hc : (Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀
      (k + 1)) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold Mloc
  rw [finsum_mem_congr rfl hterm, finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.smul_sum,
    Finset.sum_comm]
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

open Classical in
/-- **The clause `eucMloc` at `j = k + 1` for the full group `fullJSymGroup L (k + 1)`**, for the
averaged, completed source terms of `localClass_termClausesM`: from the per-site identity
`localClass_site_Mloc_eq` (inputs `hchart`, `hDM`) and the covariance of the per-site density `𝒟_M`
under the full group (`hDMfull`, P4 (H.7):
`ℳ^{(k+1)}(r x; r ψ, r h, r g) = ℳ^{(k+1)}(x; ψ, h, g)`). -/
theorem localClass_eucMloc_site {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
    [Fintype (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1))]
    {a : ℕ → ℝ} {ν : ℝ} {εseq : ℕ → ℝ}
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁ m₁ (k + 1)))
    (Tm : Terms d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁)))
    (cpl : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ Y p, cpl Y p = Classical.epsilon
      (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
          (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2 ∧
        ∀ z ∈ Y,
          q.1 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).1 z ∧
          q.2 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).2 z))
    (TM : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hTMloc : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → ∀ g, TM x Y (p, g) = TM x Y (p', g))
    (AM : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hAM : ∀ x Y q, AM x Y q =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        TM (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.2),
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.2))
    (hM : ∀ x Y Ψ h g, Tm.M (k + 1) x Y Ψ h g = AM x Y ((Ψ, h), g))
    (hchart : ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2)
    (DM : CTorus d L N₁ m₁ (k + 1) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hDM : ∀ x (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      ∑ᶠ Y ∈ polysAt P.m₀ (k + 1) x, TM x Y (q, g) = DM x (q, g))
    (hDMfull : ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1),
      ∀ x (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      DM (r x) ((actField r q.1, actField r q.2), actField r g) = DM x (q, g)) :
    ∀ hjk : k + 1 ≤ k + 1, ∀ x,
      ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1), ∀ Ψ h g,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) hjk) Ψ h →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) hjk)
        (actField r Ψ) (actField r h) →
      Mloc P.m₀ Tm (k + 1) (r x) (actField r Ψ) (actField r h) (actField r g) =
        Mloc P.m₀ Tm (k + 1) x Ψ h g := by
  intro _ x r hr Ψ h g h1 h2
  have hle : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1) ≤
      fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) :=
    symGroupBy_le_of_dvd pow_dvd_cellSide (cellSide_pos (L := L) P.m₀ m₁ (k + 1))
  have e1 := localClass_site_Mloc_eq hN Yp Tm cpl hcpl TM hTMloc AM hAM hM hchart DM hDM
    (fun r hr' => hDMfull r (hle hr')) (r x) (p := (actField r Ψ, actField r h)) h2 (actField r g)
  have e2 := localClass_site_Mloc_eq hN Yp Tm cpl hcpl TM hTMloc AM hAM hM hchart DM hDM
    (fun r hr' => hDMfull r (hle hr')) x (p := (Ψ, h)) h1 g
  simp only at e1 e2
  rw [e1, e2]
  exact hDMfull r hr x (Ψ, h) g h1 h2

end CentreClass

end Balaban.Localization
