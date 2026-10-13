/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.V2Energy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Members of `IsSF2` with a non-zero energy term at a prescribed level (package `GeneralClassWitness`)

Inventory of the landed non-zero members (`Balaban/Inhabited/V2Energy.lean`, `V2Wide.lean`).

* `eTerms`: generating set `levelGS j` (the whole-lattice set of level `j`) for every polymer; the
  energy `ℰ^{(j)}(y, X; ψ, h) = c · avg_z (h(z)·h(z) - 1)²` is non-zero only on the torus `N₁ = 1`,
  at the top level `j = k` of the torus index, on the polymer `X = 𝕋`.  Its value vanishes at every
  constant unit field `h ≡ e` with `e·e = 1`.
* `pinTerms…`: generating set `levelGS j`; no energy (`ℰ = 0`), a field-dependent source term
  `ℳ^{(j)}(x, X; ψ, h, g) = c_j e^{-κ|X|²}(h(x)·h(x) - 1) h(x)` on `X = 𝕋`.

Mismatches with the landed step witness `witnessSetting` (`d = L = 3`, `N₁ = 6`, `k = 1`, `N = 2`,
torus index `k + 1 = 2`, `a₁ = 1`, `ν = 0`, `h₀ = e₀`): (1) `eTerms` needs `N₁ = 1`, the step has
`N₁ = 6`; (2) its energy sits at the top level `j = k + 1 = 2` of the torus index, whereas the
path predicates only evaluate the old terms at the scales `1 ≤ j ≤ k = 1`; (3) its energy vanishes
at the step's reference field `h ≡ e₀` (the term vanishes to second order on the unit sphere, which
is how the landed construction meets the renormalization condition (H.5)), so even at a scale
`j ≤ k` it vanishes along the whole path, where `h` is the constant `e₀` (this is
`composedPairAtC_h_witness` in `GeneralClassWitnessStep`).

This file therefore re-instantiates the construction: `qTerms` has the `ℳ`-part and the generating
sets of `pinTerms`, and the energy
`ℰ^{(j)}(y, X; ψ, h) = c · avg_z (h(z)·h(z))` on the whole-torus polymer `X = 𝕋` at one prescribed
level `j₀`, on every torus.  Torus independence and the renormalization conditions (H.5) are
not clauses of `IsSF2` (they belong to `IsSFFamily2`); they are not claimed here, and the energy
`h·h` does not vanish at the unit sphere, so these terms are **not** a member of `IsSFFamily2`.
That is the one deviation from the landed `eTerms`, and it is forced by (3).

* `qTerms`, `isSF2_qTerms`: `IsSF2` for these terms on any field domain on which `h` is bounded by
  `2` at the level generating sets, with the same hypotheses as `isSF2_eTerms`.
* `E_qTerms_const_ne_zero`: the energy term is non-zero at every constant field `h ≡ v` with
  `v·v ≠ 0`.
* `boundedFieldDom`: the field domain of all pairs `(Ψ, h)` with `‖h(x)‖ ≤ 2`.  It is **not** the
  source chart `Ξ^c_j`; it is a domain on which the term clauses of `qTerms` hold (it contains
  `Ξ^c_j(𝔹_j; 1, ε_j)` whenever `ε_j ≤ μ/2`, `0 < μ ≤ 1`, by `vn_le_two_of_xiDom`).
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Finset Matrix

/-! ### The core function -/

section Core

variable {N : ℕ}

/-- The quadratic form `v·v = ∑ v_l²`: `O(N)`-invariant and analytic. -/
def qCore (v : Fin N → ℂ) : ℂ := ∑ l, v l * v l

theorem qCore_analyticAt (v : Fin N → ℂ) : AnalyticAt ℂ (qCore (N := N)) v := by
  have h := Finset.analyticAt_sum (𝕜 := ℂ)
    (f := fun (l : Fin N) (v : Fin N → ℂ) => v l * v l) (c := v) Finset.univ
    (fun l _ => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) l).analyticAt v).mul
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) l).analyticAt v))
  have e : (∑ l : Fin N, fun v : Fin N → ℂ => v l * v l) = fun v => ∑ l, v l * v l := by
    funext v; simp [Finset.sum_apply]
  rw [e] at h
  exact h

theorem qCore_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (v : Fin N → ℂ) :
    qCore (R *ᵥ v) = qCore v := by
  unfold qCore
  rw [bilin_vec hR v v]

theorem qCore_im {v : Fin N → ℂ} (hv : ∀ l, (v l).im = 0) : (qCore v).im = 0 := by
  unfold qCore
  rw [Complex.im_sum]
  simp [Complex.mul_im, hv]

theorem norm_qCore_le {v : Fin N → ℂ} {B : ℝ} (hB : vn v ≤ B) : ‖qCore v‖ ≤ B ^ 2 := by
  have h0 := vn_nonneg v
  unfold qCore
  calc ‖∑ l, v l * v l‖ ≤ ∑ l, ‖v l * v l‖ := norm_sum_le _ _
    _ = vn v ^ 2 := by rw [vn_sq]; exact Finset.sum_congr rfl fun l _ => by rw [norm_mul, sq]
    _ ≤ B ^ 2 := by nlinarith

end Core

/-! ### The terms -/

section Terms

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The average `|𝕋|⁻¹ ∑_z h(z)·h(z)`. -/
noncomputable def qAvg (h : Fld d L N₁ m₁ k N) : ℂ :=
  ((Fintype.card (CTorus d L N₁ m₁ k) : ℂ))⁻¹ * ∑ z, qCore (h z)

theorem qAvg_act (r : Equiv.Perm (CTorus d L N₁ m₁ k)) (h : Fld d L N₁ m₁ k N) :
    qAvg (actField r h) = qAvg h := by
  unfold qAvg actField
  rw [Equiv.sum_comp r.symm (fun z => qCore (h z))]

theorem qAvg_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (h : Fld d L N₁ m₁ k N) :
    qAvg (rotField R h) = qAvg h := by
  unfold qAvg rotField
  simp only [qCore_rot hR]

theorem qAvg_const (v : Fin N → ℂ) :
    qAvg (constFld (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) v) = qCore v := by
  unfold qAvg constFld
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : ((Fintype.card (CTorus d L N₁ m₁ k) : ℂ)) ≠ 0 := by
    have : 0 < Fintype.card (CTorus d L N₁ m₁ k) := Fintype.card_pos
    exact_mod_cast this.ne'
  field_simp

theorem norm_qAvg_le {h : Fld d L N₁ m₁ k N} {B : ℝ} (hB : ∀ z, vn (h z) ≤ B) :
    ‖qAvg h‖ ≤ B ^ 2 := by
  unfold qAvg
  have hc : 0 < Fintype.card (CTorus d L N₁ m₁ k) := Fintype.card_pos
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hs : ‖∑ z, qCore (h z)‖ ≤ (Fintype.card (CTorus d L N₁ m₁ k) : ℝ) * B ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun z _ => norm_qCore_le (hB z)).trans ?_
    simp
  have hc' : (0 : ℝ) < Fintype.card (CTorus d L N₁ m₁ k) := by exact_mod_cast hc
  calc (Fintype.card (CTorus d L N₁ m₁ k) : ℝ)⁻¹ * ‖∑ z, qCore (h z)‖
      ≤ (Fintype.card (CTorus d L N₁ m₁ k) : ℝ)⁻¹ *
        ((Fintype.card (CTorus d L N₁ m₁ k) : ℝ) * B ^ 2) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = B ^ 2 := by field_simp

theorem qAvg_im {h : Fld d L N₁ m₁ k N} (hh : ∀ z l, (h z l).im = 0) : (qAvg h).im = 0 := by
  unfold qAvg
  have h1 : (∑ z, qCore (h z)).im = 0 := by
    rw [Complex.im_sum]; exact Finset.sum_eq_zero fun z _ => qCore_im (hh z)
  have h2 : (((Fintype.card (CTorus d L N₁ m₁ k) : ℂ))⁻¹).im = 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]; exact Complex.ofReal_im _
  rw [Complex.mul_im, h1, h2]; simp

theorem analyticAt_qAvg_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] Fld d L N₁ m₁ k N) (p : E) :
    AnalyticAt ℂ (fun q : E => qAvg (T q)) p := by
  unfold qAvg
  have h := Finset.analyticAt_sum (𝕜 := ℂ)
    (f := fun (z : CTorus d L N₁ m₁ k) (q : E) => qCore (T q z)) (c := p) Finset.univ
    (fun z _ => by
      set P : E →L[ℂ] (Fin N → ℂ) :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : CTorus d L N₁ m₁ k => Fin N → ℂ) z).comp T
        with hP
      exact (qCore_analyticAt (P p)).comp (P.analyticAt p))
  have e : (∑ z : CTorus d L N₁ m₁ k, fun q : E => qCore (T q z)) =
      fun q => ∑ z, qCore (T q z) := by
    funext q; simp [Finset.sum_apply]
  rw [e] at h
  exact analyticAt_const.mul h

/-- The coefficient of the energy term at the level `j`. -/
noncomputable def cQ (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] (P : Consts) (j : ℕ) : ℝ :=
  P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j (Set.univ : Set (CTorus d L N₁ m₁ k))) / 4

theorem cQ_nonneg {P : Consts} (hE₀ : 0 ≤ P.E₀) (j : ℕ) : 0 ≤ cQ d L N₁ m₁ k P j := by
  unfold cQ; positivity

/-- **The terms with a non-zero energy at the level `j₀`** (on every torus): the `ℳ`-part and the
generating sets of `pinTerms`, and `ℰ^{(j₀)}(y, 𝕋; Ψ, h) = c · avg_z h(z)·h(z)` on the whole-torus
polymer at the level `j₀`, `c = E₀ e^{-κ d_{j₀}(𝕋)}/4`; zero otherwise. -/
noncomputable def qTerms (d L N₁ m₁ k N : ℕ) [NeZero L] [NeZero N₁] (ϱ : ℝ) (P : Consts)
    (cj : ℕ → ℝ) (j₀ : ℕ) : Terms d L N₁ m₁ k N ϱ :=
  { pinTerms d L N₁ m₁ k N ϱ P.κ cj with
    E := fun j _ X _ h =>
      open Classical in
      if j = j₀ ∧ X = Set.univ then ((cQ d L N₁ m₁ k P j : ℝ) : ℂ) * qAvg h else 0 }

theorem qTerms_gs {P : Consts} {cj : ℕ → ℝ} {j₀ j : ℕ} (hjk : j ≤ k)
    (X : Set (CTorus d L N₁ m₁ k)) :
    (qTerms d L N₁ m₁ k N ϱ P cj j₀).gs j X = levelGS j hjk := by
  simp [qTerms, pinTerms, hjk]

theorem E_qTerms (P : Consts) (cj : ℕ → ℝ) (j₀ j : ℕ) (y : CTorus d L N₁ m₁ k)
    (X : Set (CTorus d L N₁ m₁ k)) (ψ h : Fld d L N₁ m₁ k N) :
    (qTerms d L N₁ m₁ k N ϱ P cj j₀).E j y X ψ h =
      open Classical in
      if j = j₀ ∧ X = Set.univ then ((cQ d L N₁ m₁ k P j : ℝ) : ℂ) * qAvg h else 0 := rfl

theorem Eloc_qTerms (P : Consts) (cj : ℕ → ℝ) (j₀ j : ℕ) (y : CTorus d L N₁ m₁ k)
    (ψ h : Fld d L N₁ m₁ k N) :
    Eloc P.m₀ (qTerms d L N₁ m₁ k N ϱ P cj j₀) j y ψ h =
      open Classical in
      if j = j₀ then ((cQ d L N₁ m₁ k P j : ℝ) : ℂ) * qAvg h else 0 := by
  classical
  unfold Eloc
  rw [finsum_mem_single_supp _ _ Set.univ (fun X hX => by simp [E_qTerms, hX])]
  have hmem : (Set.univ : Set (CTorus d L N₁ m₁ k)) ∈ polysAt P.m₀ j y :=
    ⟨isPolyDom_univ P.m₀ j, Set.mem_univ y⟩
  simp only [hmem, ↓reduceIte, E_qTerms, and_true]

theorem Mloc_qTerms (P : Consts) (cj : ℕ → ℝ) (j₀ j : ℕ) (x : CTorus d L N₁ m₁ k)
    (Ψ h g : Fld d L N₁ m₁ k N) :
    Mloc P.m₀ (qTerms d L N₁ m₁ k N ϱ P cj j₀) j x Ψ h g =
      Mloc P.m₀ (pinTerms d L N₁ m₁ k N ϱ P.κ cj) j x Ψ h g := rfl

/-- **The term clauses for `qTerms`**, on every field domain on which the field is bounded by `2`
at the level generating sets. -/
theorem qTerms_clauses {P : Consts} {cj : ℕ → ℝ} {j₀ : ℕ}
    {Dom : FieldDom d L N₁ m₁ k N ϱ}
    (hE₀ : 0 ≤ P.E₀) (hκ : 0 ≤ P.κ) (hc0 : ∀ j, 0 ≤ cj j)
    (hc : ∀ j, 20 * cj j ≤ P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hc9 : ∀ j, 0 < P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hB : ∀ j, 1 ≤ j → ∀ (hjk : j ≤ k) Ψ h, Dom.dom j (levelGS j hjk) Ψ h → ∀ x, vn (h x) ≤ 2) :
    SFTermClauses P Dom (qTerms d L N₁ m₁ k N ϱ P cj j₀) := by
  classical
  have hM := pinTerms_clausesB (Dom := Dom) hE₀ hκ hc0 hc hc9
    (fun j hj1 hjk _ Ψ h hd x => hB j hj1 hjk Ψ h hd x)
  refine
    { gs_spec := hM.gs_spec
      analyticE := ?_
      analyticM := hM.analyticM
      rotE := ?_
      pavingGS := hM.pavingGS
      eucE := ?_
      eucEloc := ?_
      rotM := hM.rotM
      eucM := hM.eucM
      eucMloc := ?_
      localE := ?_
      localM := hM.localM
      boundE := ?_
      boundM := hM.boundM }
  · intro j _ _ y X _ _ p _
    simp only [E_qTerms]
    split_ifs
    · have h1 := analyticAt_qAvg_comp (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (N := N)
        (E := Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N)
        ((ContinuousLinearMap.snd ℂ (Fld d L N₁ m₁ k N) (Fld d L N₁ m₁ k N))) p
      exact analyticAt_const.mul h1
    · exact analyticAt_const
  · intro j _ _ y X _ _ R hR Ψ h _ _
    simp only [E_qTerms]
    rw [qAvg_rot hR.1]
  · intro j _ _ y X _ _ r _ Ψ h _ _
    simp only [E_qTerms]
    have hX : (r '' X = Set.univ) ↔ X = Set.univ := by
      constructor
      · intro h1
        have : X = r.symm '' (r '' X) := by
          rw [Set.image_image]; simp
        rw [this, h1]; simp
      · intro h1; rw [h1]; simp
    simp only [hX, qAvg_act]
  · intro j _ hjk y r _ Ψ h _ _
    rw [Eloc_qTerms, Eloc_qTerms, qAvg_act]
  · intro j hj1 hjk x r hr Ψ h g h1 h2
    exact hM.eucMloc j hj1 hjk x r hr Ψ h g h1 h2
  · intro j y X Ψ Ψ' h h' hloc
    simp only [E_qTerms]
    by_cases hX : X = Set.univ
    · have : h = h' := funext fun x => (hloc x (hX ▸ Set.mem_univ x)).2
      rw [this]
    · simp [hX]
  · intro j hj1 hjk y X hX _ Ψ h hd
    rw [qTerms_gs hjk] at hd
    simp only [E_qTerms]
    split_ifs with hc'
    · obtain ⟨_, rfl⟩ := hc'
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (cQ_nonneg hE₀ j)]
      have h1 := norm_qAvg_le (B := 2) (hB j hj1 hjk Ψ h hd)
      have h2 : ‖qAvg h‖ ≤ 4 := by nlinarith
      have h3 : cQ d L N₁ m₁ k P j * 4 = P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j (Set.univ : Set (CTorus d L N₁ m₁ k))) := by
        unfold cQ; ring
      calc cQ d L N₁ m₁ k P j * ‖qAvg h‖ ≤ cQ d L N₁ m₁ k P j * 4 :=
            mul_le_mul_of_nonneg_left h2 (cQ_nonneg hE₀ j)
        _ = _ := h3
    · rw [norm_zero]; exact mul_nonneg hE₀ (Real.exp_pos _).le

/-- **`qTerms` is a member of `IsSF2`** (density `rho2`, `Ek = 0`) on every field domain on which
the field is bounded by `2` at the level generating sets; the hypotheses are those of
`isSF2_eTerms`. -/
theorem isSF2_qTerms {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ} {cj : ℕ → ℝ} {j₀ : ℕ}
    {Dom : FieldDom d L N₁ m₁ k N ϱ} (hE₀ : 0 ≤ P.E₀) (hκ : 0 ≤ P.κ) (hc0 : ∀ j, 0 ≤ cj j)
    (hc : ∀ j, 20 * cj j ≤ P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hc9 : ∀ j, 0 < P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hB : ∀ j, 1 ≤ j → ∀ (hjk : j ≤ k) Ψ h, Dom.dom j (levelGS j hjk) Ψ h → ∀ x, vn (h x) ≤ 2)
    (H : BgHyp d L k ϱ (aIdeal L k (a k)) (Rg.sfBgMass k)) :
    IsSF2 P Rg β a Dom (qTerms d L N₁ m₁ k N ϱ P cj j₀)
      (rho2 P Rg β a (qTerms d L N₁ m₁ k N ϱ P cj j₀) 0) 0 := by
  refine isSF2_rho2 (qTerms_clauses hE₀ hκ hc0 hc hc9 hB)
    (fun j hj1 hjk X _ => by
      rw [qTerms_gs hjk]; exact GsSpec.levelGS_strong hj1 hjk X) ?_
  intro Ψ₀ h₀ g D hD
  have hDh : ∀ x i, (D.h x i).im = 0 := realizes_h_im hD.1
  have h1 := im_Fcomp_zero H hD.2.1 P.m₀ g
  rw [Fcomp_zero] at h1
  have hF : (Fcomp P.m₀ (qTerms d L N₁ m₁ k N ϱ P cj j₀) (aIdeal L k (a k)) (Rg.sfBgMass k) D
      (fun x i => (g x i : ℂ))).im = 0 := by
    unfold Fcomp
    rw [Complex.add_im, h1, zero_add, Complex.im_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    unfold Floc
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Mloc_qTerms, Mloc_pinTerms]
    have h2 := mCore_im (fun l => composedPair_h_im (a := aIdeal L k (a k)) (ν := Rg.sfBgMass k)
      hDh j x l) i
    simp [Complex.mul_im, h2]
  have hE : (Ecomp P.m₀ (qTerms d L N₁ m₁ k N ϱ P cj j₀) (aIdeal L k (a k)) (Rg.sfBgMass k) D).im
      = 0 := by
    unfold Ecomp Edens
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [Eloc_qTerms]
    split_ifs
    · have h3 := qAvg_im (h := (composedPair (aIdeal L k (a k)) (Rg.sfBgMass k) j D).2)
        (fun z l => composedPair_h_im (a := aIdeal L k (a k)) (ν := Rg.sfBgMass k) hDh j z l)
      simp [Complex.mul_im, h3]
    · simp
  unfold expo2
  simp [Complex.add_im, Complex.mul_im, hF, hE]

/-- **The energy term is not zero** at every constant field `h ≡ v` with `v·v ≠ 0`, on the
whole-torus polymer at the level `j₀`, with `E₀ > 0`; on every torus. -/
theorem E_qTerms_const_ne_zero {P : Consts} {cj : ℕ → ℝ} {j₀ : ℕ} (hE₀ : 0 < P.E₀)
    (y : CTorus d L N₁ m₁ k) (Ψ : Fld d L N₁ m₁ k N) {v : Fin N → ℂ} (hv : qCore v ≠ 0) :
    (qTerms d L N₁ m₁ k N ϱ P cj j₀).E j₀ y Set.univ Ψ (constFld v) ≠ 0 := by
  classical
  have hcond : j₀ = j₀ ∧ (Set.univ : Set (CTorus d L N₁ m₁ k)) = Set.univ := ⟨rfl, rfl⟩
  rw [E_qTerms, ite_eq_left_iff.2 (fun h => absurd hcond h), qAvg_const]
  have hc : (cQ d L N₁ m₁ k P j₀ : ℂ) ≠ 0 := by
    have : 0 < cQ d L N₁ m₁ k P j₀ := by unfold cQ; positivity
    exact_mod_cast this.ne'
  exact mul_ne_zero hc hv

end Terms

/-- **The bounded-field domain**: all real external fields, and the complex pairs `(Ψ, h)` with
`‖h(x)‖ ≤ 2` at every site.  It is not the source chart `Ξ^c_j`; it contains
`Ξ^c_j(𝔹_j; 1, ε_j)` at a mass `0 < μ ≤ 1` with `ε_j ≤ μ/2` (`vn_le_two_of_xiDom`). -/
def boundedFieldDom (d L N₁ m₁ k N : ℕ) [NeZero L] [NeZero N₁] (ϱ : ℝ) :
    FieldDom d L N₁ m₁ k N ϱ where
  phys := Set.univ
  dom := fun _ _ _ h => ∀ x, vn (h x) ≤ 2

end Balaban.SmallField.Def6v2
