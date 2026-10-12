/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2Source
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Def-6 v2: members of the second version of the class -- DRAFT

**Draft, pending Roland's answer to Q13.**  Inhabitation of `IsSF2`, `IsSFFamily2`, `SourceForm`
(hard rule 10), at choices that are not degenerate in the respects changed by CLASS-RULINGS-2:

* **the regime** is genuine: the scale `k` may lie at or below the switch (`k ≤ k₀`), where the
  background mass is `0` and the physical mass `ν_k L^{-2k} > 0` stays in the action
  (`isSFFamily2_pin_witness`, any `k₀`);
* **the pinned radius** `r_h ∈ (0, 1]` is positive, the pinned field is the coordinate vector
  `e₀`;
* **the terms `ℳ^{(j)}` depend on the field `h`**: `pinTerms` has
  `ℳ^{(j)}(x, X; Ψ, h, g) = c_j e^{-κ |X|²} (h(x)·h(x) - 1) h(x)` on the whole-torus polymer `X = 𝕋`
  (`0` on the other polymers), an `O(N)`-equivariant, Euclidean-covariant, local term, bounded on
  the pinned domain (`‖h‖ < 1 + r_h`) and **unbounded on the landed domain at zero background
  mass**, where `h` is unrestricted.  Its constant-spin response is not zero
  (`pinTerms_M_const_ne_zero`), and `𝕋` is a polymer of `𝒟_j` (`isPolyDom_univ`).

The terms `ℰ^{(j)}` of this member are zero: a nonzero `ℰ` must be torus independent on
non-winding polymers (`TorusIndep`), which excludes whole-torus terms, and needs the single-cell
geometry of `𝒟_j`; this is not done here.  A second family of members is obtained from the landed
class by the restriction theorem (`isSFFamily2_of_landed_witness`).

* `isPolyDom_univ`, `torus_reach`: the whole torus is a polymer;
* `mCore`, `wCoef`, `pinTerms`, `Mloc_pinTerms`: the terms; `pinTerms_clauses`: `SFTermClauses`;
* `rho2`, `isSF2_rho2`: the density of the second version for terms with a real exponent;
* `isSF2_pinTerms`, `isSFFamily2_pin_witness`, `sourceForm_pin_witness`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Finset Matrix

/-! ### The whole torus is a polymer -/

section Geometry

theorem single_eq_nsmul {d n : ℕ} [NeZero n] (μ : Fin d) (c : ZMod n) :
    (Pi.single μ c : Torus d n) = c.val • (Pi.single μ 1 : Torus d n) := by
  funext ν
  by_cases h : ν = μ
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

/-- The torus is nearest-neighbour connected. -/
theorem torus_reach {d n : ℕ} [NeZero n] (x y : Torus d n) :
    Relation.ReflTransGen (fun a b : Torus d n => a ∈ (Set.univ : Set (Torus d n)) ∧
      b ∈ (Set.univ : Set (Torus d n)) ∧ Nbr a b) x y := by
  have step : ∀ (z : Torus d n) (μ : Fin d) (c : ℕ), Relation.ReflTransGen
      (fun a b : Torus d n => a ∈ (Set.univ : Set (Torus d n)) ∧
        b ∈ (Set.univ : Set (Torus d n)) ∧ Nbr a b) z (z + c • (Pi.single μ 1 : Torus d n)) := by
    intro z μ c
    induction c with
    | zero => rw [zero_nsmul, add_zero]
    | succ c ih =>
      refine ih.tail ⟨trivial, trivial, μ, Or.inl ?_⟩
      rw [succ_nsmul, add_assoc]
  have key : ∀ (v : Torus d n) (s : Finset (Fin d)), Relation.ReflTransGen
      (fun a b : Torus d n => a ∈ (Set.univ : Set (Torus d n)) ∧
        b ∈ (Set.univ : Set (Torus d n)) ∧ Nbr a b) x
      (x + ∑ μ ∈ s, (Pi.single μ (v μ) : Torus d n)) := by
    intro v s
    classical
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, add_zero]
    | insert μ s hμ ih =>
      have e : x + ((Pi.single μ (v μ) : Torus d n) + ∑ ν ∈ s, (Pi.single ν (v ν) : Torus d n)) =
          (x + ∑ ν ∈ s, (Pi.single ν (v ν) : Torus d n)) +
            (v μ).val • (Pi.single μ 1 : Torus d n) := by
        rw [← single_eq_nsmul]; abel
      rw [Finset.sum_insert hμ, e]
      exact ih.trans (step _ μ _)
  have := key (y - x) Finset.univ
  rw [Finset.univ_sum_single] at this
  simpa using this

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- **The whole torus is a polymer of `𝒟_j`** (the union of all `π'_j`-cubes). -/
theorem isPolyDom_univ (m₀ j : ℕ) :
    IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) m₀ j Set.univ := by
  have hcs : 0 < cellSide L m₀ m₁ j := cellSide_pos m₀ m₁ j
  have hL : 1 ≤ L := Nat.pos_of_ne_zero (NeZero.ne L)
  refine ⟨⟨0, trivial⟩, ⟨{b | Aligned (cellSide L m₀ m₁ j) b}, ⟨fun b hb =>
    ⟨hb, Set.subset_univ _⟩, fun z _ => ⟨cbase (cellSide L m₀ m₁ j) z, aligned_cbase z, ?_⟩⟩⟩,
    fun x _ y _ => torus_reach x y⟩
  exact box_mono _ (Nat.le_mul_of_pos_left _ hL) (mem_box_cbase hcs z)

end Geometry

/-! ### The field-dependent term -/

section Core

variable {N : ℕ}

/-- `m(v) = (v·v - 1) v`: the `O(N)`-equivariant cubic vanishing on the unit sphere. -/
def mCore (v : Fin N → ℂ) : Fin N → ℂ := (∑ l, v l * v l - 1) • v

theorem mCore_analyticAt (v : Fin N → ℂ) : AnalyticAt ℂ (mCore (N := N)) v := by
  have h := Finset.analyticAt_sum (𝕜 := ℂ)
    (f := fun (l : Fin N) (v : Fin N → ℂ) => v l * v l) (c := v) Finset.univ
    (fun l _ => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) l).analyticAt v).mul
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) l).analyticAt v))
  have e : (∑ l : Fin N, fun v : Fin N → ℂ => v l * v l) = fun v => ∑ l, v l * v l := by
    funext v; simp [Finset.sum_apply]
  rw [e] at h
  exact (h.sub analyticAt_const).smul analyticAt_id

theorem mCore_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (v : Fin N → ℂ) :
    mCore (R *ᵥ v) = R *ᵥ mCore v := by
  unfold mCore
  rw [bilin_vec hR v v, Matrix.mulVec_smul]

theorem mCore_unit {v : Fin N → ℝ} (hv : v ⬝ᵥ v = 1) : mCore (fun i => (v i : ℂ)) = 0 := by
  unfold mCore
  have : (∑ l, (v l : ℂ) * (v l : ℂ)) = 1 := by
    have h : ((v ⬝ᵥ v : ℝ) : ℂ) = 1 := by rw [hv]; simp
    rw [← h]; simp [dotProduct]
  rw [this, sub_self, zero_smul]

theorem mCore_im {v : Fin N → ℂ} (hv : ∀ l, (v l).im = 0) (i : Fin N) : (mCore v i).im = 0 := by
  have e : v = fun l => (((v l).re : ℝ) : ℂ) :=
    funext fun l => Complex.ext (by simp) (by simp [hv l])
  have h2 : mCore (fun l => (((v l).re : ℝ) : ℂ)) i =
      (((∑ l, (v l).re * (v l).re - 1) * (v i).re : ℝ) : ℂ) := by
    simp [mCore]
  rw [e, h2, Complex.ofReal_im]

theorem vn_smul_c (c : ℂ) (v : Fin N → ℂ) : vn (c • v) = ‖c‖ * vn v := by
  unfold vn; rw [WithLp.toLp_smul, norm_smul]

theorem vn_mCore_le {v : Fin N → ℂ} {B : ℝ} (hB : vn v ≤ B) :
    vn (mCore v) ≤ (B ^ 2 + 1) * B := by
  have h0 := vn_nonneg v
  unfold mCore
  rw [vn_smul_c]
  have h1 : ‖∑ l, v l * v l - 1‖ ≤ B ^ 2 + 1 := by
    calc ‖∑ l, v l * v l - 1‖ ≤ ‖∑ l, v l * v l‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ ∑ l, ‖v l‖ ^ 2 + 1 := by
        rw [norm_one]
        refine add_le_add_left ((norm_sum_le _ _).trans (le_of_eq ?_)) 1
        exact Finset.sum_congr rfl fun l _ => by rw [norm_mul, sq]
      _ = vn v ^ 2 + 1 := by rw [vn_sq]
      _ ≤ B ^ 2 + 1 := by nlinarith
  exact mul_le_mul h1 hB h0 (by positivity)

theorem mCore_smul_single (i₀ : Fin N) (t : ℂ) :
    mCore (t • (Pi.single i₀ 1 : Fin N → ℂ)) = ((t ^ 2 - 1) * t) • Pi.single i₀ 1 := by
  unfold mCore
  have : ∑ l, (t • (Pi.single i₀ 1 : Fin N → ℂ)) l * (t • (Pi.single i₀ 1 : Fin N → ℂ)) l =
      t ^ 2 := by
    rw [Finset.sum_eq_single i₀]
    · simp [sq]
    · intro l _ hl; simp [Pi.single_eq_of_ne hl]
    · simp
  rw [this, smul_smul]

end Core

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- The weight of the term: `c_j e^{-κ |X|²}` on the whole-torus polymer, `0` on the others
(`|X|² ≥ d_j(X)`, `sizeJ_le_ncard_sq`). -/
noncomputable def wCoef (κ : ℝ) (cj : ℕ → ℝ) (j : ℕ) (X : Set (CTorus d L N₁ m₁ k)) : ℝ :=
  if X = Set.univ then cj j * Real.exp (-κ * (X.ncard : ℝ) ^ 2) else 0

omit [NeZero L] [NeZero N₁] in
theorem wCoef_nonneg {κ : ℝ} {cj : ℕ → ℝ} (hc : ∀ j, 0 ≤ cj j) (j : ℕ)
    (X : Set (CTorus d L N₁ m₁ k)) : 0 ≤ wCoef κ cj j X := by
  unfold wCoef; split_ifs
  · exact mul_nonneg (hc j) (Real.exp_pos _).le
  · exact le_rfl

omit [NeZero L] [NeZero N₁] in
theorem wCoef_image (κ : ℝ) (cj : ℕ → ℝ) (j : ℕ) (r : Equiv.Perm (CTorus d L N₁ m₁ k))
    (X : Set (CTorus d L N₁ m₁ k)) : wCoef κ cj j (r '' X) = wCoef κ cj j X := by
  have h : r '' X = Set.univ ↔ X = Set.univ := by
    constructor
    · intro h
      have := congrArg (fun S => r.symm '' S) h
      simpa [Equiv.symm_image_image, Set.image_univ_of_surjective r.symm.surjective] using this
    · rintro rfl; exact Set.image_univ_of_surjective r.surjective
  unfold wCoef
  simp only [h, Set.ncard_image_of_injective _ r.injective]

theorem wCoef_le {κ : ℝ} {cj : ℕ → ℝ} (hκ : 0 ≤ κ) (hc : ∀ j, 0 ≤ cj j) {m₀ j : ℕ}
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom m₀ j X) :
    wCoef κ cj j X ≤ cj j * Real.exp (-κ * sizeJ m₀ j X) := by
  unfold wCoef; split_ifs
  · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hc j)
    have := sizeJ_le_ncard_sq hX
    nlinarith
  · exact mul_nonneg (hc j) (Real.exp_pos _).le

/-- **The terms of the field-dependent member**: `ℰ = 0`,
`ℳ^{(j)}(x, X; Ψ, h, g) = c_j e^{-κ|X|²} (h(x)·h(x) - 1) h(x)` for `X = 𝕋` (and `0` otherwise),
`𝔹_j(X)` the whole-lattice generating set of level `j`. -/
noncomputable def pinTerms (d L N₁ m₁ k N : ℕ) [NeZero L] [NeZero N₁] (ϱ κ : ℝ) (cj : ℕ → ℝ) :
    Terms d L N₁ m₁ k N ϱ where
  E := fun _ _ _ _ _ => 0
  M := fun j x X _ h _ => ((wCoef κ cj j X : ℝ) : ℂ) • mCore (h x)
  gs := fun j _ => if h : j ≤ k then levelGS j h else topGS d L N₁ m₁ k ϱ

theorem pinTerms_gs {κ : ℝ} {cj : ℕ → ℝ} {j : ℕ} (hjk : j ≤ k) (X : Set (CTorus d L N₁ m₁ k)) :
    (pinTerms d L N₁ m₁ k N ϱ κ cj).gs j X = levelGS j hjk := by
  simp [pinTerms, hjk]

theorem finsum_mem_single_supp {α M : Type*} [AddCommMonoid M] (S : Set α) (f : α → M) (a : α)
    (h : ∀ x, x ≠ a → f x = 0) :
    ∑ᶠ x ∈ S, f x = open Classical in if a ∈ S then f a else 0 := by
  classical
  rw [finsum_mem_def, finsum_eq_single _ a (fun x hx => by simp [Set.indicator, h x hx])]
  simp [Set.indicator]

/-- The density `ℳ^{(j)}(x; Ψ, h, g)` of the field-dependent member: the whole-torus term. -/
theorem Mloc_pinTerms (m₀ : ℕ) (κ : ℝ) (cj : ℕ → ℝ) (j : ℕ) (x : CTorus d L N₁ m₁ k)
    (Ψ h g : Fld d L N₁ m₁ k N) :
    Mloc m₀ (pinTerms d L N₁ m₁ k N ϱ κ cj) j x Ψ h g =
      ((wCoef κ cj j (Set.univ : Set (CTorus d L N₁ m₁ k)) : ℝ) : ℂ) • mCore (h x) := by
  unfold Mloc
  rw [finsum_mem_single_supp _ _ Set.univ (fun X hX => by simp [pinTerms, wCoef, hX])]
  have hmem : (Set.univ : Set (CTorus d L N₁ m₁ k)) ∈ polysAt m₀ j x :=
    ⟨isPolyDom_univ m₀ j, Set.mem_univ x⟩
  simp only [hmem, ↓reduceIte]
  rfl

theorem Eloc_pinTerms (m₀ : ℕ) (κ : ℝ) (cj : ℕ → ℝ) (j : ℕ) (y : CTorus d L N₁ m₁ k)
    (ψ h : Fld d L N₁ m₁ k N) : Eloc m₀ (pinTerms d L N₁ m₁ k N ϱ κ cj) j y ψ h = 0 := by
  simp [Eloc, pinTerms]

/-- **The constant-spin response of the field-dependent member is not zero**: at the constant
field `h = (1 + s) e`, `s > 0` (inside the pinned ball for `s < r_h`), on the whole-torus polymer. -/
theorem pinTerms_M_const_ne_zero {κ : ℝ} {cj : ℕ → ℝ} {j : ℕ} (hc : 0 < cj j) (i₀ : Fin N)
    {s : ℝ} (hs : 0 < s) (x : CTorus d L N₁ m₁ k) (Ψ g : Fld d L N₁ m₁ k N) :
    (pinTerms d L N₁ m₁ k N ϱ κ cj).M j x Set.univ Ψ
      (constFld (((1 + s : ℝ) : ℂ) • Pi.single i₀ 1)) g ≠ 0 := by
  show ((wCoef κ cj j (Set.univ : Set (CTorus d L N₁ m₁ k)) : ℝ) : ℂ) •
    mCore (((1 + s : ℝ) : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ)) ≠ 0
  rw [mCore_smul_single, smul_smul]
  intro h
  have h1 := congrFun h i₀
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Pi.zero_apply] at h1
  have hw : wCoef κ cj j (Set.univ : Set (CTorus d L N₁ m₁ k)) ≠ 0 := by
    simp only [wCoef, ↓reduceIte]; positivity
  have h2 : ((1 + s : ℝ) : ℂ) ^ 2 - 1 ≠ 0 := by
    have : ((1 + s) ^ 2 - 1 : ℝ) ≠ 0 := by nlinarith
    exact_mod_cast this
  have h3 : ((1 + s : ℝ) : ℂ) ≠ 0 := by
    have : (1 + s : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  have h4 : ((wCoef κ cj j (Set.univ : Set (CTorus d L N₁ m₁ k)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hw
  exact mul_ne_zero h4 (mul_ne_zero h2 h3) h1

/-- **The field-dependent terms satisfy the term clauses** on every field domain on which the
field is bounded by `2` (`‖h‖ ≤ B_h = 1 + r_h ≤ 2` on the pinned domain), with
`20 c_j ≤ c₉ L^{-j((d-2)/2+γ-α₁)}`.  On the landed domain at zero background mass the clause
`boundM` fails for them (the field is unbounded there). -/
theorem pinTerms_clauses {P : Consts} {cj : ℕ → ℝ} {Dom : FieldDom d L N₁ m₁ k N ϱ}
    (hE₀ : 0 ≤ P.E₀) (hκ : 0 ≤ P.κ) (hc0 : ∀ j, 0 ≤ cj j)
    (hc : ∀ j, 20 * cj j ≤ P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hc9 : ∀ j, 0 < P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hB : ∀ j G Ψ h, Dom.dom j G Ψ h → ∀ x, vn (h x) ≤ 2) :
    SFTermClauses P Dom (pinTerms d L N₁ m₁ k N ϱ P.κ cj) where
  gs_spec := by
    intro j hj1 hjk X _
    rw [pinTerms_gs hjk]
    refine ⟨?_, ?_⟩
    · intro x _
      simp [levelGS, hj1]
    · intro i hi
      have : ¬ i ≤ j := by omega
      simp [levelGS, this]
  analyticE := fun j _ _ y X _ _ => analyticOnNhd_const
  analyticM := fun j _ _ x X _ _ p _ => by
    set T : (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N) →L[ℂ] (Fin N → ℂ) :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : CTorus d L N₁ m₁ k => Fin N → ℂ) x).comp
        ((ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)) with hT
    have h1 : AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
        mCore (T p)) p := (mCore_analyticAt (T p)).comp (T.analyticAt p)
    have h0 : AnalyticAt ℂ (fun _ : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
        ((wCoef P.κ cj j X : ℝ) : ℂ)) p := analyticAt_const
    exact h0.smul h1
  rotE := by intros; rfl
  pavingGS := by
    intro j hj1 hjk X _ r _ i
    rw [pinTerms_gs hjk, pinTerms_gs hjk]
    by_cases hi : i ≤ j <;> simp [levelGS, hi]
  eucE := by intros; rfl
  eucEloc := by
    intro j _ hjk y r _ Ψ h _ _
    rw [Eloc_pinTerms, Eloc_pinTerms]
  rotM := by
    intro j _ _ x X _ _ R hR Ψ h g _ _
    show ((wCoef P.κ cj j X : ℝ) : ℂ) • mCore (R *ᵥ h x) =
      R *ᵥ (((wCoef P.κ cj j X : ℝ) : ℂ) • mCore (h x))
    rw [mCore_rot hR.1, Matrix.mulVec_smul]
  eucM := by
    intro j _ _ x X _ _ r _ Ψ h g _ _
    show ((wCoef P.κ cj j (r '' X) : ℝ) : ℂ) • mCore (h (r.symm (r x))) =
      ((wCoef P.κ cj j X : ℝ) : ℂ) • mCore (h x)
    rw [wCoef_image, Equiv.symm_apply_apply]
  eucMloc := by
    intro j _ hjk x r _ Ψ h g _ _
    rw [Mloc_pinTerms, Mloc_pinTerms]
    show _ • mCore (h (r.symm (r x))) = _
    rw [Equiv.symm_apply_apply]
  localE := by intros; rfl
  localM := by
    intro j x X Ψ Ψ' h h' g g' hloc
    show ((wCoef P.κ cj j X : ℝ) : ℂ) • mCore (h x) = ((wCoef P.κ cj j X : ℝ) : ℂ) • mCore (h' x)
    by_cases hX : X = Set.univ
    · rw [(hloc x (hX ▸ Set.mem_univ x)).2.1]
    · simp [wCoef, hX]
  boundE := by
    intro j _ _ y X _ _ Ψ h _
    show ‖(0 : ℂ)‖ ≤ _
    rw [norm_zero]
    exact mul_nonneg hE₀ (Real.exp_pos _).le
  boundM := by
    intro j _ _ x X hX _ Ψ h g hd _
    show vn (((wCoef P.κ cj j X : ℝ) : ℂ) • mCore (h x)) < _
    rw [vn_smul_c, Complex.norm_real, Real.norm_of_nonneg (wCoef_nonneg hc0 j X)]
    have h1 := vn_mCore_le (hB j _ Ψ h hd x)
    have h2 := wCoef_le hκ hc0 (m₀ := P.m₀) hX
    have h3 := wCoef_nonneg (κ := P.κ) hc0 j X
    have he := Real.exp_pos (-P.κ * sizeJ P.m₀ j X)
    have h4 : wCoef P.κ cj j X * vn (mCore (h x)) ≤
        cj j * Real.exp (-P.κ * sizeJ P.m₀ j X) * ((2 ^ 2 + 1) * 2) :=
      mul_le_mul h2 h1 (vn_nonneg _) (mul_nonneg (hc0 j) he.le)
    have h5 := hc j
    have h6 := hc9 j
    nlinarith [mul_pos h6 he, mul_le_mul_of_nonneg_right h5 he.le]

/-! ### The density of the second version for terms with a real exponent -/

open Classical in
/-- **The real density of the second version** for given terms: `χ_k exp(Re expo2)` at the
realizing datum (the exponent is real for real terms). -/
noncomputable def rho2 (P : Consts) (Rg : Regime L) (β a : ℕ → ℝ) (Tm : Terms d L N₁ m₁ k N ϱ)
    (Ek : ℝ) (Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ)
    (g : CTorus d L N₁ m₁ k → Fin N → ℝ) : ℝ :=
  if hX : Xi (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg.bgMass k) k 1
      (P.p (β k) / Real.sqrt (β k)) Ψ₀ h₀
  then Real.exp (expo2 P Rg β a Tm Ek (Classical.choose hX.2.2) (fun x i => (g x i : ℂ))).re
  else 0

/-- Terms satisfying the term clauses and whose exponent is real at the real data of the support
of `χ_k` form a member of `IsSF2`, with the density `rho2`. -/
theorem isSF2_rho2 {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ} {Dom : FieldDom d L N₁ m₁ k N ϱ}
    {Tm : Terms d L N₁ m₁ k N ϱ} {Ek : ℝ} (hT : SFTermClauses P Dom Tm)
    (hreal : ∀ (Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ)
      (g : CTorus d L N₁ m₁ k → Fin N → ℝ) (D : BgData (topGS d L N₁ m₁ k ϱ) N),
      XiAt (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg.bgMass k) k 1
        (P.p (β k) / Real.sqrt (β k)) D Ψ₀ h₀ →
      (expo2 P Rg β a Tm Ek D (fun x i => (g x i : ℂ))).im = 0) :
    IsSF2 P Rg β a Dom Tm (rho2 P Rg β a Tm Ek) Ek where
  terms := hT
  density := by
    intro Ψ₀ h₀ g D _ hD _
    classical
    unfold rho2
    by_cases hX : Xi (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg.bgMass k) k 1
        (P.p (β k) / Real.sqrt (β k)) Ψ₀ h₀
    · simp only [hX, ↓reduceDIte, ↓reduceIte]
      have hD0 := Classical.choose_spec hX.2.2
      have hDD : D = Classical.choose hX.2.2 := realizes_unique hD hD0.1
      rw [← hDD] at hD0 ⊢
      have him := hreal Ψ₀ h₀ g D hD0
      have hw : expo2 P Rg β a Tm Ek D (fun x i => (g x i : ℂ)) =
          (((expo2 P Rg β a Tm Ek D (fun x i => (g x i : ℂ))).re : ℝ) : ℂ) :=
        Complex.ext (by simp) (by simpa using him)
      conv_rhs => rw [hw]
      rw [← Complex.ofReal_exp]
    · simp only [hX, ↓reduceDIte, ↓reduceIte]; simp

omit [NeZero N₁] in
theorem realizes_h_im {N₀ : ℕ} [NeZero N₀] {G : GeneratingSet d L N₀ k ϱ} {D : BgData G N}
    {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ} (hR : Realizes D Ψ₀ h₀)
    (x : Torus d (N₀ * L ^ k)) (i : Fin N) : (D.h x i).im = 0 := by
  by_cases hx : x ∈ G.Ω 1
  · rw [hR.2 x hx i]; simp
  · rw [D.h_zero x hx]; simp

theorem composedPair_h_im {a : ℕ → ℝ} {ν : ℝ} {D : BgData (topGS d L N₁ m₁ k ϱ) N}
    (hD : ∀ x i, (D.h x i).im = 0) (j : ℕ) (x : CTorus d L N₁ m₁ k) (i : Fin N) :
    ((composedPair a ν j D).2 x i).im = 0 := by
  unfold composedPair
  split_ifs with hj
  · simp only [composedData, composeData]
    split_ifs
    · exact hD x i
    · simp
  · simp

/-- **The field-dependent terms form a member of `IsSF2`** on every field domain on which the
field is bounded by `2`, for every regime, with the density `rho2`. -/
theorem isSF2_pinTerms {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ} {cj : ℕ → ℝ}
    {Dom : FieldDom d L N₁ m₁ k N ϱ} (hE₀ : 0 ≤ P.E₀) (hκ : 0 ≤ P.κ) (hc0 : ∀ j, 0 ≤ cj j)
    (hc : ∀ j, 20 * cj j ≤ P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hc9 : ∀ j, 0 < P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hB : ∀ j G Ψ h, Dom.dom j G Ψ h → ∀ x, vn (h x) ≤ 2)
    (H : BgHyp d L k ϱ (aIdeal L k (a k)) (Rg.bgMass k)) :
    IsSF2 P Rg β a Dom (pinTerms d L N₁ m₁ k N ϱ P.κ cj)
      (rho2 P Rg β a (pinTerms d L N₁ m₁ k N ϱ P.κ cj) 0) 0 := by
  refine isSF2_rho2 (pinTerms_clauses hE₀ hκ hc0 hc hc9 hB) ?_
  intro Ψ₀ h₀ g D hD
  have hDh : ∀ x i, (D.h x i).im = 0 := realizes_h_im hD.1
  have h1 := im_Fcomp_zero H hD.2.1 P.m₀ g
  rw [Fcomp_zero] at h1
  have hF : (Fcomp P.m₀ (pinTerms d L N₁ m₁ k N ϱ P.κ cj) (aIdeal L k (a k)) (Rg.bgMass k) D
      (fun x i => (g x i : ℂ))).im = 0 := by
    unfold Fcomp
    rw [Complex.add_im, h1, zero_add, Complex.im_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    unfold Floc
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Mloc_pinTerms]
    have h2 := mCore_im (fun l => composedPair_h_im (a := aIdeal L k (a k)) (ν := Rg.bgMass k)
      hDh j x l) i
    simp [Complex.mul_im, h2]
  have hE : Ecomp P.m₀ (pinTerms d L N₁ m₁ k N ϱ P.κ cj) (aIdeal L k (a k)) (Rg.bgMass k) D = 0 := by
    simp [Ecomp, Edens, Eloc_pinTerms]
  unfold expo2
  rw [hE]
  simp [Complex.add_im, Complex.mul_im, hF]

/-! ### Members of the class of families -/

section Family

theorem torusIndep_pinTerms (m₀ : ℕ) (κ : ℝ) (cj : ℕ → ℝ) :
    TorusIndep (d := d) (L := L) (m₁ := m₁) (k := k) (N := N) (ϱ := ϱ) m₀
      (fun N₁ _ => pinTerms d L N₁ m₁ k N ϱ κ cj) where
  E_eq := by intros; rfl

theorem ElocInf_pinTerms (m₀ : ℕ) (κ : ℝ) (cj : ℕ → ℝ) (j : ℕ) (y : Fin d → ℤ)
    (ψ h : InfFld d N) :
    ElocInf (L := L) (m₁ := m₁) (k := k) (ϱ := ϱ) m₀
      (fun N₁ _ => pinTerms d L N₁ m₁ k N ϱ κ cj) j y ψ h = 0 := by
  have hE : ∀ X' : Finset (Fin d → ℤ), Einf (L := L) (m₁ := m₁) (k := k) (ϱ := ϱ) m₀
      (fun N₁ _ => pinTerms d L N₁ m₁ k N ϱ κ cj) j y X' ψ h = 0 := fun X' => by
    unfold Einf
    exact stabVal_eq (Filter.Eventually.of_forall fun n => rfl)
  unfold ElocInf
  simp [hE]

theorem renormCond_pinTerms (m₀ k' : ℕ) (νk κ : ℝ) (cj : ℕ → ℝ) (j : ℕ) :
    RenormCond (d := d) (L := L) (m₁ := m₁) (N := N) (ϱ := ϱ) m₀ k' νk
      (fun N₁ _ => pinTerms d L N₁ m₁ k' N ϱ κ cj) j where
  val := fun i₀ => ElocInf_pinTerms _ _ _ _ _ _ _
  dh := by
    intro i₀ _
    simp [ElocInf_pinTerms]
  dpsi := by
    intro i₀
    simp [ElocInf_pinTerms]
  moment := by
    intro i₀ i₁ _
    have : ∀ n : ℕ, (haveI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
      momentSum m₀ (pinTerms d L (n + 1) m₁ k' N ϱ κ cj) j i₀ i₁) = 0 := by
      intro n
      have hD : ∀ (c v w : Fld d L (n + 1) m₁ k' N),
          D2 (fun ψ : Fld d L (n + 1) m₁ k' N => (0 : ℂ)) c v w = 0 := by
        intro c v w; simp [D2]
      simp [momentSum, Edens, Eloc_pinTerms, hD]
    simp only [this]
    exact tendsto_const_nhds

/-- The weight sequence of the witness: `c_j = L^{-2j} / 20`. -/
noncomputable def witCj (L : ℕ) : ℕ → ℝ := fun j => 1 / 20 * (((L : ℝ) ^ j)⁻¹) ^ 2

theorem witCj_pos (j : ℕ) : 0 < witCj L j := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold witCj; positivity

theorem witCj_le {c₉ s : ℝ} (hc : 1 ≤ c₉) (hs : s ≤ 2) (j : ℕ) :
    20 * witCj L j ≤ c₉ * ((L : ℝ) ^ j)⁻¹ ^ s := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hx0 : 0 < ((L : ℝ) ^ j)⁻¹ := by positivity
  have hx1 : ((L : ℝ) ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL)
  have h1 : (((L : ℝ) ^ j)⁻¹) ^ (2 : ℝ) ≤ ((L : ℝ) ^ j)⁻¹ ^ s :=
    Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hs
  rw [Real.rpow_two] at h1
  have h2 : 0 < ((L : ℝ) ^ j)⁻¹ ^ s := Real.rpow_pos_of_pos hx0 s
  unfold witCj
  nlinarith

/-- **A member of the second version of the class of families with field-dependent terms, on the
pinned domain** (`d = L = 3`, `N = 2`, any `m₁`, `k`, any switch index `k₀`, `ϱ ≥ R₀(3,3)`, pinned
field `e₀`, pin radius `0 < r_h ≤ 1`): the constants and running coefficients of the landed
witness (`β_n = 3^n`, `ν_n = (7/72) 9^{n-k}`, `a_n = 5/4`), the regime `(k₀, ν)`, the terms
`pinTerms` and the density `rho2`.  For `k ≤ k₀` the background mass is `0` and the physical mass
`ν_k 9^{-k} > 0` is in the action. -/
theorem isSFFamily2_pin_witness (m₁ k k₀ : ℕ) (ϱ : ℝ) (hϱ : bgR0 3 3 ≤ ϱ) {α₀ rH : ℝ}
    (hα : 0 < α₀) (hr1 : rH ≤ 1) :
    IsSFFamily2 (d := 3) (L := 3) (m₁ := m₁) (k := k) (N := 2) (ϱ := ϱ) (witnessConsts α₀)
      ⟨k₀, witnessν k⟩ witnessβ witnessa
      (fun _ _ => pinFieldDom (Pi.single 0 1) rH (aIdeal 3 k (witnessa k))
        (bgMassAt 3 k₀ k (witnessν k k)) ((witnessConsts α₀).eps 3 3))
      (fun N₁ _ => pinTerms 3 3 N₁ m₁ k 2 ϱ (witnessConsts α₀).κ (witCj 3))
      (fun N₁ _ => rho2 (witnessConsts α₀) ⟨k₀, witnessν k⟩ witnessβ witnessa
        (pinTerms 3 3 N₁ m₁ k 2 ϱ (witnessConsts α₀).κ (witCj 3)) 0) (fun _ => 0) where
  admissible := witnessConsts_admissible hα
  coeff := witness_coeff k
  torus := fun N₁ _ => by
    have hκ : 0 ≤ (witnessConsts α₀).κ := (witnessConsts_admissible hα).κ_pos.le
    have hs : (((3 : ℕ) : ℝ) - 2) / 2 + (witnessConsts α₀).γ - (witnessConsts α₀).α₁ ≤ 2 := by
      norm_num [witnessConsts]
    refine isSF2_pinTerms le_rfl hκ (fun j => (witCj_pos j).le)
      (fun j => witCj_le (by norm_num [witnessConsts]) hs j) (fun j => ?_) (fun j G Ψ h hd x => ?_)
      (bgHyp_of_class2 (witnessConsts_admissible hα) (witness_coeff k) le_rfl le_rfl hϱ)
    · have hx0 : (0 : ℝ) < (((3 : ℕ) : ℝ) ^ j)⁻¹ := by positivity
      have := Real.rpow_pos_of_pos hx0
        ((((3 : ℕ) : ℝ) - 2) / 2 + (witnessConsts α₀).γ - (witnessConsts α₀).α₁)
      simp only [witnessConsts, one_mul] at this ⊢
      exact this
    · have hp : Pin (Pi.single 0 1) rH G (aIdeal 3 k (witnessa k))
          (bgMassAt 3 k₀ k (witnessν k k)) j ((witnessConsts α₀).eps 3 3 j) Ψ h := hd
      linarith [hp.vn_lt x]
  torusIndep := torusIndep_pinTerms _ _ _
  renorm := fun _ _ _ => renormCond_pinTerms _ _ _ _ _ _

/-- **Members of the second version from the landed witness** (restriction theorem (c)): for
`k ≤ 2` the landed witness has running-test mass `0` (`β_k ν_k = 3^k · 7/72 ≤ 1`); with a switch
index `k₀ ≥ k` it gives a member of the second version on the pinned domain at every `h_*`, with
the physical mass `(7/72) 9^{-k} > 0` in the action. -/
theorem isSFFamily2_of_landed_witness (m₁ k j k₀ : ℕ) (ϱ : ℝ) (hϱ : bgR0 3 3 ≤ ϱ) (hk : k ≤ 2)
    (hk₀ : k ≤ k₀) (hStar : Fin 2 → ℝ) (rH : ℝ) :
    ∃ ρ : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus 3 3 N₁ m₁ k → Fin 2 → ℝ) → (Fin 2 → ℝ) →
        (CTorus 3 3 N₁ m₁ k → Fin 2 → ℝ) → ℝ,
      IsSFFamily2 (d := 3) (L := 3) (m₁ := m₁) (k := k) (N := 2) (ϱ := ϱ)
        (witnessConsts (witnessα₀ j)) ⟨k₀, witnessν k⟩ witnessβ witnessa
        (fun _ _ => pinFieldDom hStar rH (aIdeal 3 k (witnessa k))
          (bgMassAt 3 k₀ k (witnessν k k)) ((witnessConsts (witnessα₀ j)).eps 3 3))
        (zeroFam 3 3 m₁ k 2 ϱ) ρ (fun _ => 0) := by
  have hβν : witnessβ k * witnessν k k ≤ 1 := by
    have e : witnessν k k = 7 / 72 := by
      simp only [witnessν]; rw [mul_div_assoc, div_self (by positivity)]; norm_num
    have h3 : witnessβ k ≤ 9 := by
      simp only [witnessβ]
      calc (3 : ℝ) ^ k ≤ 3 ^ 2 := pow_le_pow_right₀ (by norm_num) hk
        _ = 9 := by norm_num
    rw [e]; linarith
  have hμ : bgMassAt 3 k₀ k (witnessν k k) = bgMass 3 k (witnessβ k) (witnessν k k) :=
    bgMassAt_eq_bgMass ⟨fun _ => hβν, fun _ => hk₀⟩
  exact ⟨_, (isSFFamily_witness m₁ k j ϱ hϱ).toPin hμ hStar rH⟩

/-- **The source form of the field-dependent member** (`ν_j > 0`): the reparametrized source
terms, with `C_D = 0` (the terms `ℰ` vanish) and the reference-jet certificate of PIN-I6. -/
theorem sourceForm_pin_witness {P : Consts} {ν : ℕ → ℝ} {cj : ℕ → ℝ}
    {Dom : FieldDom d L N₁ m₁ k N ϱ} (hα : 0 < P.α₀) (hE₀ : 0 ≤ P.E₀) (hκ : 0 ≤ P.κ)
    (hc0 : ∀ j, 0 ≤ cj j)
    (hc : ∀ j, 20 * cj j ≤ P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hc9 : ∀ j, 0 < P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hB : ∀ j G Ψ h, Dom.dom j G Ψ h → ∀ x, vn (h x) ≤ 2) (hν : 0 < ν k) (i₀ : Fin N) :
    SourceForm P ν Dom (pinTerms d L N₁ m₁ k N ϱ P.κ cj)
      (sourceOf ν (pinTerms d L N₁ m₁ k N ϱ P.κ cj)) i₀ 0 := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine sourceForm_of_pos (pinTerms_clauses hE₀ hκ hc0 hc hc9 hB)
    (fun j _ _ => by unfold nuIdeal; positivity) (fun j _ _ y X _ _ u => ?_)
    (fun j _ _ X' _ => ?_)
  · have e : (fun b : Fin N → ℂ => (sourceOf ν (pinTerms d L N₁ m₁ k N ϱ P.κ cj)).E j y X
        (constFld (Pi.single i₀ 1)) (constFld b)) = fun _ => (0 : ℂ) := rfl
    rw [e]
    simp
  · have hr : 0 < anisoRadius d L N P j := by
      have hε := eps_pos (d := d) (L := L) hα j
      have hK := bgK1_pos d L N
      have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos i₀
      unfold anisoRadius rotB
      positivity
    have e : srcPack (sourceOf ν (pinTerms d L N₁ m₁ k N ϱ P.κ cj)) j i₀ X' =
        fun _ => (0 : ℂ) := rfl
    rw [e]
    refine (refJet_const i₀ _ hr X' 0).mono hr ?_
    rw [norm_zero]
    exact mul_nonneg hE₀ (Real.exp_pos _).le

end Family

end Balaban.SmallField.Def6v2
