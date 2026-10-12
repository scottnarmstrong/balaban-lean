/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.V2Wide
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Def-6 v2: members of the class with a nonzero energy term `ℰ`

The energy terms are supported on the whole-torus polymer of the torus `N₁ = 1` at the level `k`,
with value `c · avg_z F(h(z))`, `F(v) = (v·v - 1)²`, an `O(N)`-invariant analytic function
vanishing to second order on the unit sphere (so that the value, the first `h`-jet and the
second transverse jet at the reference point `(e, e)` are zero).  Torus independence holds
because a polymer of the torus `N₁ = 1` that is the whole torus and a polymer of another torus
`N₂ ≥ 2` with the same lift cannot exist (cardinalities, `torusIndep_eTerms`); the infinite-volume
density is zero.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Finset Matrix

/-! ### The core function -/

section Core

variable {N : ℕ}

/-- `F(v) = (v·v - 1)²`: `O(N)`-invariant, vanishing to second order on the unit sphere. -/
def fCore (v : Fin N → ℂ) : ℂ := (∑ l, v l * v l - 1) ^ 2

theorem fCore_analyticAt (v : Fin N → ℂ) : AnalyticAt ℂ (fCore (N := N)) v := by
  have h := Finset.analyticAt_sum (𝕜 := ℂ)
    (f := fun (l : Fin N) (v : Fin N → ℂ) => v l * v l) (c := v) Finset.univ
    (fun l _ => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) l).analyticAt v).mul
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) l).analyticAt v))
  have e : (∑ l : Fin N, fun v : Fin N → ℂ => v l * v l) = fun v => ∑ l, v l * v l := by
    funext v; simp [Finset.sum_apply]
  rw [e] at h
  exact (h.sub analyticAt_const).pow 2

theorem fCore_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (v : Fin N → ℂ) :
    fCore (R *ᵥ v) = fCore v := by
  unfold fCore
  rw [bilin_vec hR v v]

theorem fCore_unit {v : Fin N → ℝ} (hv : v ⬝ᵥ v = 1) : fCore (fun i => (v i : ℂ)) = 0 := by
  unfold fCore
  have : (∑ l, (v l : ℂ) * (v l : ℂ)) = 1 := by
    have h : ((v ⬝ᵥ v : ℝ) : ℂ) = 1 := by rw [hv]; simp
    rw [← h]; simp [dotProduct]
  rw [this, sub_self]; simp

theorem fCore_im {v : Fin N → ℂ} (hv : ∀ l, (v l).im = 0) : (fCore v).im = 0 := by
  unfold fCore
  have h1 : (∑ l, v l * v l - 1).im = 0 := by
    rw [Complex.sub_im, Complex.im_sum]
    simp [Complex.mul_im, hv]
  rw [pow_two, Complex.mul_im, h1]; simp

theorem norm_fCore_le {v : Fin N → ℂ} {B : ℝ} (hB : vn v ≤ B) : ‖fCore v‖ ≤ (B ^ 2 + 1) ^ 2 := by
  have h0 := vn_nonneg v
  unfold fCore
  rw [norm_pow]
  have h1 : ‖∑ l, v l * v l - 1‖ ≤ B ^ 2 + 1 := by
    calc ‖∑ l, v l * v l - 1‖ ≤ ‖∑ l, v l * v l‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ ∑ l, ‖v l‖ ^ 2 + 1 := by
        rw [norm_one]
        refine add_le_add_left ((norm_sum_le _ _).trans (le_of_eq ?_)) 1
        exact Finset.sum_congr rfl fun l _ => by rw [norm_mul, sq]
      _ = vn v ^ 2 + 1 := by rw [vn_sq]
      _ ≤ B ^ 2 + 1 := by nlinarith
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

end Core

/-! ### The terms -/

section Terms

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The average `|𝕋|⁻¹ Σ_z F(h(z))`. -/
noncomputable def eAvg (h : Fld d L N₁ m₁ k N) : ℂ :=
  ((Fintype.card (CTorus d L N₁ m₁ k) : ℂ))⁻¹ * ∑ z, fCore (h z)

theorem eAvg_act (r : Equiv.Perm (CTorus d L N₁ m₁ k)) (h : Fld d L N₁ m₁ k N) :
    eAvg (actField r h) = eAvg h := by
  unfold eAvg actField
  rw [Equiv.sum_comp r.symm (fun z => fCore (h z))]

theorem eAvg_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (h : Fld d L N₁ m₁ k N) :
    eAvg (rotField R h) = eAvg h := by
  unfold eAvg rotField
  simp only [fCore_rot hR]

theorem eAvg_const (v : Fin N → ℂ) :
    eAvg (constFld (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) v) = fCore v := by
  unfold eAvg constFld
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : ((Fintype.card (CTorus d L N₁ m₁ k) : ℂ)) ≠ 0 := by
    have : 0 < Fintype.card (CTorus d L N₁ m₁ k) := Fintype.card_pos
    exact_mod_cast this.ne'
  field_simp

theorem norm_eAvg_le {h : Fld d L N₁ m₁ k N} {B : ℝ} (hB : ∀ z, vn (h z) ≤ B) :
    ‖eAvg h‖ ≤ (B ^ 2 + 1) ^ 2 := by
  unfold eAvg
  have hc : 0 < Fintype.card (CTorus d L N₁ m₁ k) := Fintype.card_pos
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hs : ‖∑ z, fCore (h z)‖ ≤ (Fintype.card (CTorus d L N₁ m₁ k) : ℝ) * (B ^ 2 + 1) ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun z _ => norm_fCore_le (hB z)).trans ?_
    simp
  have hc' : (0 : ℝ) < Fintype.card (CTorus d L N₁ m₁ k) := by exact_mod_cast hc
  calc (Fintype.card (CTorus d L N₁ m₁ k) : ℝ)⁻¹ * ‖∑ z, fCore (h z)‖
      ≤ (Fintype.card (CTorus d L N₁ m₁ k) : ℝ)⁻¹ *
        ((Fintype.card (CTorus d L N₁ m₁ k) : ℝ) * (B ^ 2 + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (B ^ 2 + 1) ^ 2 := by field_simp

theorem eAvg_im {h : Fld d L N₁ m₁ k N} (hh : ∀ z l, (h z l).im = 0) : (eAvg h).im = 0 := by
  unfold eAvg
  have h1 : (∑ z, fCore (h z)).im = 0 := by
    rw [Complex.im_sum]; exact Finset.sum_eq_zero fun z _ => fCore_im (hh z)
  have h2 : (((Fintype.card (CTorus d L N₁ m₁ k) : ℂ))⁻¹).im = 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]; exact Complex.ofReal_im _
  rw [Complex.mul_im, h1, h2]; simp

theorem analyticAt_eAvg_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] Fld d L N₁ m₁ k N) (p : E) :
    AnalyticAt ℂ (fun q : E => eAvg (T q)) p := by
  unfold eAvg
  have h := Finset.analyticAt_sum (𝕜 := ℂ)
    (f := fun (z : CTorus d L N₁ m₁ k) (q : E) => fCore (T q z)) (c := p) Finset.univ
    (fun z _ => by
      set P : E →L[ℂ] (Fin N → ℂ) :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : CTorus d L N₁ m₁ k => Fin N → ℂ) z).comp T
        with hP
      exact (fCore_analyticAt (P p)).comp (P.analyticAt p))
  have e : (∑ z : CTorus d L N₁ m₁ k, fun q : E => fCore (T q z)) =
      fun q => ∑ z, fCore (T q z) := by
    funext q; simp [Finset.sum_apply]
  rw [e] at h
  exact analyticAt_const.mul h

/-- **The terms with a nonzero energy**: the `ℳ`-part of `pinTerms`, the generating sets of
`pinTerms`, and `ℰ^{(k)}(y, 𝕋; Ψ, h) = c · avg F(h)` on the whole-torus polymer of the torus
`N₁ = 1` at the level `k` (`c = E₀ e^{-κ d_k(𝕋)} / 25`), zero otherwise. -/
noncomputable def eTerms (d L N₁ m₁ k N : ℕ) [NeZero L] [NeZero N₁] (ϱ : ℝ) (P : Consts)
    (cj : ℕ → ℝ) : Terms d L N₁ m₁ k N ϱ :=
  { pinTerms d L N₁ m₁ k N ϱ P.κ cj with
    E := fun j _ X _ h =>
      open Classical in
      if N₁ = 1 ∧ j = k ∧ X = Set.univ then
        ((P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ k (Set.univ : Set (CTorus d L N₁ m₁ k))) / 25 : ℝ) : ℂ) *
          eAvg h
      else 0 }

theorem eTerms_gs {P : Consts} {cj : ℕ → ℝ} {j : ℕ} (hjk : j ≤ k) (X : Set (CTorus d L N₁ m₁ k)) :
    (eTerms d L N₁ m₁ k N ϱ P cj).gs j X = levelGS j hjk := by
  simp [eTerms, pinTerms, hjk]

/-- The coefficient of the energy term. -/
noncomputable def cEn (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] (P : Consts) : ℝ :=
  P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ k (Set.univ : Set (CTorus d L N₁ m₁ k))) / 25

theorem cEn_nonneg {P : Consts} (hE₀ : 0 ≤ P.E₀) : 0 ≤ cEn d L N₁ m₁ k P := by
  unfold cEn; positivity

theorem E_eTerms (P : Consts) (cj : ℕ → ℝ) (j : ℕ) (y : CTorus d L N₁ m₁ k)
    (X : Set (CTorus d L N₁ m₁ k)) (ψ h : Fld d L N₁ m₁ k N) :
    (eTerms d L N₁ m₁ k N ϱ P cj).E j y X ψ h =
      open Classical in
      if N₁ = 1 ∧ j = k ∧ X = Set.univ then ((cEn d L N₁ m₁ k P : ℝ) : ℂ) * eAvg h else 0 := rfl

theorem M_eTerms (P : Consts) (cj : ℕ → ℝ) :
    (eTerms d L N₁ m₁ k N ϱ P cj).M = (pinTerms d L N₁ m₁ k N ϱ P.κ cj).M := rfl

theorem Eloc_eTerms (P : Consts) (cj : ℕ → ℝ) (j : ℕ) (y : CTorus d L N₁ m₁ k)
    (ψ h : Fld d L N₁ m₁ k N) :
    Eloc P.m₀ (eTerms d L N₁ m₁ k N ϱ P cj) j y ψ h =
      open Classical in
      if N₁ = 1 ∧ j = k then ((cEn d L N₁ m₁ k P : ℝ) : ℂ) * eAvg h else 0 := by
  classical
  unfold Eloc
  rw [finsum_mem_single_supp _ _ Set.univ (fun X hX => by simp [E_eTerms, hX])]
  have hmem : (Set.univ : Set (CTorus d L N₁ m₁ k)) ∈ polysAt P.m₀ j y :=
    ⟨isPolyDom_univ P.m₀ j, Set.mem_univ y⟩
  simp only [hmem, ↓reduceIte, E_eTerms, and_true]

theorem Mloc_eTerms (P : Consts) (cj : ℕ → ℝ) (j : ℕ) (x : CTorus d L N₁ m₁ k)
    (Ψ h g : Fld d L N₁ m₁ k N) :
    Mloc P.m₀ (eTerms d L N₁ m₁ k N ϱ P cj) j x Ψ h g =
      Mloc P.m₀ (pinTerms d L N₁ m₁ k N ϱ P.κ cj) j x Ψ h g := rfl

/-- **The term clauses for the terms with a nonzero energy**, on every field domain on which the
field is bounded by `2` at the level generating sets. -/
theorem eTerms_clauses {P : Consts} {cj : ℕ → ℝ} {Dom : FieldDom d L N₁ m₁ k N ϱ}
    (hE₀ : 0 ≤ P.E₀) (hκ : 0 ≤ P.κ) (hc0 : ∀ j, 0 ≤ cj j)
    (hc : ∀ j, 20 * cj j ≤ P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hc9 : ∀ j, 0 < P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hB : ∀ j, 1 ≤ j → ∀ (hjk : j ≤ k) Ψ h, Dom.dom j (levelGS j hjk) Ψ h → ∀ x, vn (h x) ≤ 2) :
    SFTermClauses P Dom (eTerms d L N₁ m₁ k N ϱ P cj) := by
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
    simp only [E_eTerms]
    split_ifs
    · have h1 := analyticAt_eAvg_comp (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (N := N)
        (E := Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N)
        ((ContinuousLinearMap.snd ℂ (Fld d L N₁ m₁ k N) (Fld d L N₁ m₁ k N))) p
      exact analyticAt_const.mul h1
    · exact analyticAt_const
  · intro j _ _ y X _ _ R hR Ψ h _ _
    simp only [E_eTerms]
    rw [eAvg_rot hR.1]
  · intro j _ _ y X _ _ r _ Ψ h _ _
    simp only [E_eTerms]
    have hX : (r '' X = Set.univ) ↔ X = Set.univ := by
      constructor
      · intro h1
        have : X = r.symm '' (r '' X) := by
          rw [Set.image_image]; simp
        rw [this, h1]; simp
      · intro h1; rw [h1]; simp
    simp only [hX, eAvg_act]
  · intro j _ hjk y r _ Ψ h _ _
    rw [Eloc_eTerms, Eloc_eTerms, eAvg_act]
  · intro j hj1 hjk x r hr Ψ h g h1 h2
    exact hM.eucMloc j hj1 hjk x r hr Ψ h g h1 h2
  · intro j y X Ψ Ψ' h h' hloc
    simp only [E_eTerms]
    by_cases hX : X = Set.univ
    · have : h = h' := funext fun x => (hloc x (hX ▸ Set.mem_univ x)).2
      rw [this]
    · simp [hX]
  · intro j hj1 hjk y X hX _ Ψ h hd
    rw [eTerms_gs hjk] at hd
    simp only [E_eTerms]
    split_ifs with hc'
    · obtain ⟨_, rfl, rfl⟩ := hc'
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (cEn_nonneg hE₀)]
      have h1 := norm_eAvg_le (B := 2) (hB j hj1 hjk Ψ h hd)
      have h2 : ‖eAvg h‖ ≤ 25 := by nlinarith
      have h3 : cEn d L N₁ m₁ j P * 25 = P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j (Set.univ : Set (CTorus d L N₁ m₁ j))) := by
        unfold cEn; ring
      calc cEn d L N₁ m₁ j P * ‖eAvg h‖ ≤ cEn d L N₁ m₁ j P * 25 :=
            mul_le_mul_of_nonneg_left h2 (cEn_nonneg hE₀)
        _ = _ := h3
    · rw [norm_zero]; exact mul_nonneg hE₀ (Real.exp_pos _).le

end Terms

/-! ### Torus independence -/

section Geometry

theorem ncard_box_ge {d n : ℕ} [NeZero n] (b : Torus d n) (s : ℕ) :
    (min s n) ^ d ≤ (box b s).ncard := by
  classical
  set t := min s n with ht
  have hts : t ≤ s := min_le_left _ _
  have htn : t ≤ n := min_le_right _ _
  let f : (Fin d → Fin t) → Torus d n := fun w => b + natT (fun μ => (w μ : ℕ))
  have hf : Function.Injective f := by
    intro w w' hww
    have h1 : (natT (fun μ => (w μ : ℕ)) : Torus d n) = natT (fun μ => (w' μ : ℕ)) :=
      add_left_cancel hww
    funext μ
    have h2 := congrFun h1 μ
    simp only [natT_apply] at h2
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    rw [Nat.mod_eq_of_lt ((w μ).2.trans_le htn), Nat.mod_eq_of_lt ((w' μ).2.trans_le htn)] at h2
    exact Fin.ext h2
  have hsub : (↑(Finset.univ.image f) : Set (Torus d n)) ⊆ box b s := by
    intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨w, rfl⟩ := hx
    exact ⟨fun μ => (w μ : ℕ), fun μ => (w μ).2.trans_le hts, rfl⟩
  calc t ^ d = (Finset.univ.image f).card := by
        rw [Finset.card_image_of_injective _ hf]; simp
    _ = (↑(Finset.univ.image f) : Set (Torus d n)).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (box b s).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

theorem isPolyDom_ncard_ge {m₀ j : ℕ} {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom m₀ j X) :
    (min (L * cellSide L m₀ m₁ j) ((N₁ * L ^ m₁) * L ^ k)) ^ d ≤ X.ncard := by
  obtain ⟨⟨z, hz⟩, ⟨𝒦, h𝒦⟩, _⟩ := hX
  obtain ⟨b, hb, hzb⟩ := h𝒦.2 z hz
  exact (ncard_box_ge b _).trans (Set.ncard_le_ncard (h𝒦.1 b hb).2 (Set.toFinite _))

theorem no_whole_poly {m₀ : ℕ} (hd : 1 ≤ d) (hL : 2 ≤ L) {X' : Finset (Fin d → ℤ)}
    (N₂ : ℕ) [NeZero N₂] (hN₂ : N₂ ≠ 1)
    (hnw₁ : NonWind L 1 m₁ k k X') (hnw₂ : NonWind L N₂ m₁ k k X')
    (h1 : Ypoly (L := L) (N₁ := 1) (m₁ := m₁) (k := k) k X' = Set.univ)
    (h2 : IsPolyDom (L := L) (N₁ := N₂) (m₁ := m₁) (k := k) m₀ k
      (Ypoly (L := L) (N₁ := N₂) (m₁ := m₁) (k := k) k X')) : False := by
  have c1 := ncard_Ypoly (L := L) (N₁ := 1) (m₁ := m₁) (k := k) (le_refl k) hnw₁
  have c2 := ncard_Ypoly (L := L) (N₁ := N₂) (m₁ := m₁) (k := k) (le_refl k) hnw₂
  rw [h1] at c1
  have hcard : (Set.univ : Set (CTorus d L 1 m₁ k)).ncard = ((1 * L ^ m₁) * L ^ k) ^ d := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card]
    simp [CTorus, Torus]
  have h3 := isPolyDom_ncard_ge h2
  rw [c2, ← c1, hcard] at h3
  have hLpos : 0 < L := by omega
  have ha : 0 < (1 * L ^ m₁) * L ^ k := by positivity
  have h4 : min (L * cellSide L m₀ m₁ k) ((N₂ * L ^ m₁) * L ^ k) ≤ (1 * L ^ m₁) * L ^ k :=
    (Nat.pow_le_pow_iff_left (by omega)).1 h3
  have hN2 : 2 ≤ N₂ := by
    have := NeZero.pos N₂; omega
  have h5 : 2 * ((1 * L ^ m₁) * L ^ k) ≤ L * cellSide L m₀ m₁ k := by
    unfold cellSide
    have : L ^ (k + m₀ + m₁) = L ^ m₁ * L ^ k * L ^ m₀ := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [this]
    have h6 : 1 ≤ L ^ m₀ := Nat.one_le_pow _ _ hLpos
    calc 2 * (1 * L ^ m₁ * L ^ k) ≤ L * (L ^ m₁ * L ^ k) := by
          rw [one_mul]; exact Nat.mul_le_mul_right _ hL
      _ ≤ L * (L ^ m₁ * L ^ k * L ^ m₀) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ h6)
  have h7 : 2 * ((1 * L ^ m₁) * L ^ k) ≤ (N₂ * L ^ m₁) * L ^ k := by
    rw [one_mul, mul_assoc]
    exact Nat.mul_le_mul_right _ hN2
  have := le_min h5 h7
  omega

end Geometry

section Indep

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **Torus independence of the energy terms**: the only polymer with a nonzero term is the whole
torus `𝕋` of the torus `N₁ = 1` at the level `k`; a polymer of another torus `N₂ ≠ 1` with the
same lift would have a different cardinality (`no_whole_poly`). -/
theorem torusIndep_eTerms (hd : 1 ≤ d) (hL : 2 ≤ L) (P : Consts) (cj : ℕ → ℝ) :
    TorusIndep (d := d) (L := L) (m₁ := m₁) (k := k) (N := N) (ϱ := ϱ) P.m₀
      (fun N₁ _ => eTerms d L N₁ m₁ k N ϱ P cj) where
  E_eq := by
    classical
    intro j hj1 hjk y X' hy ψ h N₁ N₂ _ _ hnw1 hnw2 hp1 hp2
    simp only [E_eTerms]
    by_cases c1 : N₁ = 1 ∧ j = k ∧ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' = Set.univ
    · by_cases c2 : N₂ = 1 ∧ j = k ∧ Ypoly (L := L) (N₁ := N₂) (m₁ := m₁) (k := k) j X' = Set.univ
      · obtain ⟨rfl, rfl, _⟩ := c1
        obtain ⟨rfl, _, _⟩ := c2
        rfl
      · exfalso
        obtain ⟨hN1, rfl, hU⟩ := c1
        subst hN1
        by_cases hN2 : N₂ = 1
        · subst hN2; exact c2 ⟨rfl, rfl, hU⟩
        · exact no_whole_poly (m₀ := P.m₀) hd hL N₂ hN2 hnw1 hnw2 hU hp2
    · by_cases c2 : N₂ = 1 ∧ j = k ∧ Ypoly (L := L) (N₁ := N₂) (m₁ := m₁) (k := k) j X' = Set.univ
      · exfalso
        obtain ⟨hN2, rfl, hU⟩ := c2
        subst hN2
        by_cases hN1 : N₁ = 1
        · subst hN1; exact c1 ⟨rfl, rfl, hU⟩
        · exact no_whole_poly (m₀ := P.m₀) hd hL N₁ hN1 hnw2 hnw1 hU hp1
      · simp [c1, c2]

end Indep

/-! ### The infinite-volume density vanishes; the renormalization conditions -/

section Renorm

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

theorem torusSeq_ne_one (m₀ n : ℕ) (hn : 1 ≤ n) : torusSeq L m₀ n ≠ 1 := by
  unfold torusSeq
  have h1 : 1 ≤ L ^ m₀ := Nat.one_le_pow _ _ (NeZero.pos L)
  have : n + 1 ≤ L ^ m₀ * (n + 1) := Nat.le_mul_of_pos_left _ h1
  omega

theorem ElocInf_eTerms (P : Consts) (cj : ℕ → ℝ) (j : ℕ) (y : Fin d → ℤ) (ψ h : InfFld d N) :
    ElocInf (L := L) (m₁ := m₁) (k := k) (ϱ := ϱ) P.m₀
      (fun N₁ _ => eTerms d L N₁ m₁ k N ϱ P cj) j y ψ h = 0 := by
  classical
  have hE : ∀ X' : Finset (Fin d → ℤ), Einf (L := L) (m₁ := m₁) (k := k) (ϱ := ϱ) P.m₀
      (fun N₁ _ => eTerms d L N₁ m₁ k N ϱ P cj) j y X' ψ h = 0 := fun X' => by
    unfold Einf
    refine stabVal_eq ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have := torusSeq_ne_one (L := L) P.m₀ n hn
    simp [Eseq, E_eTerms, this]
  unfold ElocInf
  simp [hE]

theorem renormCond_eTerms (P : Consts) (k' : ℕ) (νk : ℝ) (cj : ℕ → ℝ) (j : ℕ) :
    RenormCond (d := d) (L := L) (m₁ := m₁) (N := N) (ϱ := ϱ) P.m₀ k' νk
      (fun N₁ _ => eTerms d L N₁ m₁ k' N ϱ P cj) j where
  val := fun i₀ => ElocInf_eTerms _ _ _ _ _ _
  dh := by
    intro i₀ _
    simp [ElocInf_eTerms]
  dpsi := by
    intro i₀
    simp [ElocInf_eTerms]
  moment := by
    intro i₀ i₁ _
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn1 : n ≠ 0 := by omega
    have hD : ∀ (c v w : Fld d L (n + 1) m₁ k' N),
        D2 (fun ψ : Fld d L (n + 1) m₁ k' N => (0 : ℂ)) c v w = 0 := by
      intro c v w; simp [D2]
    symm
    have : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
    simp [momentSum, Edens, Eloc_eTerms, hn1, hD]

end Renorm

/-! ### Members of the class with nonzero energy -/

section Member

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

theorem fCore_smul_single {N : ℕ} (i₀ : Fin N) (t : ℂ) :
    fCore (t • (Pi.single i₀ 1 : Fin N → ℂ)) = (t ^ 2 - 1) ^ 2 := by
  unfold fCore
  congr 2
  simp [Pi.single_apply, sq]

/-- **The energy terms are not zero**: at the constant field `h = t e_{i₀}` with `t² ≠ 1`, on the
whole-torus polymer of the torus `N₁ = 1` at the level `k`, with `E₀ > 0`. -/
theorem E_eTerms_const_ne_zero {P : Consts} {cj : ℕ → ℝ} (hE₀ : 0 < P.E₀) (hN : N₁ = 1)
    (y : CTorus d L N₁ m₁ k) (Ψ : Fld d L N₁ m₁ k N) (i₀ : Fin N) {t : ℂ} (ht : t ^ 2 ≠ 1) :
    (eTerms d L N₁ m₁ k N ϱ P cj).E k y Set.univ Ψ
      (constFld (t • (Pi.single i₀ 1 : Fin N → ℂ))) ≠ 0 := by
  classical
  have hcond : N₁ = 1 ∧ k = k ∧ (Set.univ : Set (CTorus d L N₁ m₁ k)) = Set.univ := ⟨hN, rfl, rfl⟩
  rw [E_eTerms, ite_eq_left_iff.2 (fun h => absurd hcond h), eAvg_const, fCore_smul_single]
  have hc : (cEn d L N₁ m₁ k P : ℂ) ≠ 0 := by
    have : 0 < cEn d L N₁ m₁ k P := by unfold cEn; positivity
    exact_mod_cast this.ne'
  exact mul_ne_zero hc (pow_ne_zero 2 (sub_ne_zero.2 ht))

theorem isSF2_eTerms {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ} {cj : ℕ → ℝ}
    {Dom : FieldDom d L N₁ m₁ k N ϱ} (hE₀ : 0 ≤ P.E₀) (hκ : 0 ≤ P.κ) (hc0 : ∀ j, 0 ≤ cj j)
    (hc : ∀ j, 20 * cj j ≤ P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hc9 : ∀ j, 0 < P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hB : ∀ j, 1 ≤ j → ∀ (hjk : j ≤ k) Ψ h, Dom.dom j (levelGS j hjk) Ψ h → ∀ x, vn (h x) ≤ 2)
    (H : BgHyp d L k ϱ (aIdeal L k (a k)) (Rg.sfBgMass k)) :
    IsSF2 P Rg β a Dom (eTerms d L N₁ m₁ k N ϱ P cj)
      (rho2 P Rg β a (eTerms d L N₁ m₁ k N ϱ P cj) 0) 0 := by
  refine isSF2_rho2 (eTerms_clauses hE₀ hκ hc0 hc hc9 hB) ?_
  intro Ψ₀ h₀ g D hD
  have hDh : ∀ x i, (D.h x i).im = 0 := realizes_h_im hD.1
  have h1 := im_Fcomp_zero H hD.2.1 P.m₀ g
  rw [Fcomp_zero] at h1
  have hF : (Fcomp P.m₀ (eTerms d L N₁ m₁ k N ϱ P cj) (aIdeal L k (a k)) (Rg.sfBgMass k) D
      (fun x i => (g x i : ℂ))).im = 0 := by
    unfold Fcomp
    rw [Complex.add_im, h1, zero_add, Complex.im_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    unfold Floc
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Mloc_eTerms, Mloc_pinTerms]
    have h2 := mCore_im (fun l => composedPair_h_im (a := aIdeal L k (a k)) (ν := Rg.sfBgMass k)
      hDh j x l) i
    simp [Complex.mul_im, h2]
  have hE : (Ecomp P.m₀ (eTerms d L N₁ m₁ k N ϱ P cj) (aIdeal L k (a k)) (Rg.sfBgMass k) D).im
      = 0 := by
    unfold Ecomp Edens
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [Eloc_eTerms]
    split_ifs
    · have h3 := eAvg_im (h := (composedPair (aIdeal L k (a k)) (Rg.sfBgMass k) j D).2)
        (fun z l => composedPair_h_im (a := aIdeal L k (a k)) (ν := Rg.sfBgMass k) hDh j z l)
      simp [Complex.mul_im, h3]
    · simp
  unfold expo2
  simp [Complex.add_im, Complex.mul_im, hF, hE]

end Member

section Nonzero

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The density `ℰ^{(k)}(y; ψ, h)` of the energy terms is not zero at a constant field off the
unit sphere (torus `N₁ = 1`, `E₀ > 0`). -/
theorem Eloc_eTerms_const_ne_zero {P : Consts} {cj : ℕ → ℝ} (hE₀ : 0 < P.E₀) (hN : N₁ = 1)
    (y : CTorus d L N₁ m₁ k) (Ψ : Fld d L N₁ m₁ k N) (i₀ : Fin N) {t : ℂ} (ht : t ^ 2 ≠ 1) :
    Eloc P.m₀ (eTerms d L N₁ m₁ k N ϱ P cj) k y Ψ
      (constFld (t • (Pi.single i₀ 1 : Fin N → ℂ))) ≠ 0 := by
  classical
  have hcond : N₁ = 1 ∧ k = k := ⟨hN, rfl⟩
  rw [Eloc_eTerms, ite_eq_left_iff.2 (fun h => absurd hcond h), eAvg_const, fCore_smul_single]
  have hc : (cEn d L N₁ m₁ k P : ℂ) ≠ 0 := by
    have : 0 < cEn d L N₁ m₁ k P := by unfold cEn; positivity
    exact_mod_cast this.ne'
  exact mul_ne_zero hc (pow_ne_zero 2 (sub_ne_zero.2 ht))

end Nonzero

/-! ### The wide-domain witness with nonzero `ℰ` and `ℳ` -/

/-- The constants of the witness with `E₀ = 1`. -/
noncomputable def eConsts (α₀ : ℝ) : Consts := { witnessConsts α₀ with E₀ := 1 }

theorem eConsts_admissible {α₀ : ℝ} (h : 0 < α₀) : (eConsts α₀).Admissible 3 3 where
  γ_pos := (witnessConsts_admissible h).γ_pos
  γ_lt := (witnessConsts_admissible h).γ_lt
  α₁_pos := (witnessConsts_admissible h).α₁_pos
  α₁_lt := (witnessConsts_admissible h).α₁_lt
  α₀_pos := (witnessConsts_admissible h).α₀_pos
  κ_pos := (witnessConsts_admissible h).κ_pos
  νbar_pos := (witnessConsts_admissible h).νbar_pos
  νbar_le := (witnessConsts_admissible h).νbar_le
  c₈_pos := (witnessConsts_admissible h).c₈_pos
  E₀_nonneg := zero_le_one

theorem eConsts_coeff (k : ℕ) {α₀ : ℝ} :
    CoeffBounds 3 3 k (eConsts α₀) witnessβ (witnessν k) witnessa where
  flow := (witness_coeff (α₀ := α₀) k).flow
  beta_gt := (witness_coeff (α₀ := α₀) k).beta_gt
  nu_pos := (witness_coeff (α₀ := α₀) k).nu_pos
  nu_le := (witness_coeff (α₀ := α₀) k).nu_le
  a_ge := (witness_coeff (α₀ := α₀) k).a_ge
  a_lt := (witness_coeff (α₀ := α₀) k).a_lt

/-- **A member of `IsSFFamily2` on the wide domain `xiFieldDom` at positive mass with nonzero
energy terms `ℰ` and nonzero source terms `ℳ`** (`d = L = 3`, `N = 2`, any `m₁`, `k`, `k₀`,
`ϱ ≥ R₀(3,3)`; `E₀ = 1`): `ℰ^{(k)}(y, 𝕋; Ψ, h) = c · avg_z (h(z)·h(z) - 1)²` on the whole-torus
polymer of the torus `N₁ = 1` (and `0` otherwise), `c = E₀ e^{-κ d_k(𝕋)}/25`;
`ℳ^{(j)}` as in `isSFFamily2_xi_witness_M`.  Torus independence: `torusIndep_eTerms`; the
infinite-volume density vanishes (`ElocInf_eTerms`). -/
theorem isSFFamily2_xi_witness_E (m₁ k k₀ : ℕ) (ϱ : ℝ) (hϱ : bgR0 3 3 ≤ ϱ) :
    IsSFFamily2 (d := 3) (L := 3) (m₁ := m₁) (k := k) (N := 2) (ϱ := ϱ)
      (eConsts (wideα₀ k)) ⟨k₀, witnessν k⟩ witnessβ witnessa
      (fun _ _ => xiFieldDom (aIdeal 3 k (witnessa k)) (physMass 3 k (witnessν k k))
        ((eConsts (wideα₀ k)).eps 3 3))
      (fun N₁ _ => eTerms 3 3 N₁ m₁ k 2 ϱ (eConsts (wideα₀ k)) (witCj 3))
      (fun N₁ _ => rho2 (eConsts (wideα₀ k)) ⟨k₀, witnessν k⟩ witnessβ witnessa
        (eTerms 3 3 N₁ m₁ k 2 ϱ (eConsts (wideα₀ k)) (witCj 3)) 0) (fun _ => 0) where
  admissible := eConsts_admissible (wideα₀_pos k)
  coeff := eConsts_coeff k
  torus := fun N₁ _ => isSF2_eTerms zero_le_one (eConsts_admissible (wideα₀_pos k)).κ_pos.le
    (fun j => (witCj_pos j).le) (witness_cj_le (wideα₀ k)) (witness_c9_pos (wideα₀ k))
    (fun j hj1 hjk Ψ h hd x => by
      refine vn_le_two_of_xiDom (physMass_witness_pos k) (physMass_witness_le_one k)
        (wide_eps_le k j) (fun x => ?_) (hd : XiDom _ _ _ _ _ Ψ h) x
      simp [levelGS, hj1])
    (bgHyp_of_class2 (eConsts_admissible (wideα₀_pos k)) (eConsts_coeff k) le_rfl le_rfl hϱ)
  torusIndep := torusIndep_eTerms (by norm_num) (by norm_num) _ _
  renorm := fun _ _ _ => renormCond_eTerms _ _ _ _ _

end Balaban.SmallField.Def6v2
