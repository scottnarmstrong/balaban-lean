module

public import Balaban.LargeField.R.ZeroDomainPaths
public import Balaban.LargeField.Geometry.Continuous
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The boundary layer of a box and its embedding in the integer grid

`shellOut Z = {x ∉ Z : d(x, Z) ≤ 1}` is the layer of `k`-blocks outside `Z` adjacent to it (adjacency in the
index distance, so that the layer of a box is connected).  For `Z = box a s` with `1 ≤ s_i` and `s_i + 2 ≤ m`,
`gridEmb a` maps the grid boundary `gridBd s` onto `shellOut (box a s)` (`gridEmb_gridBd_eq`), and the
steps of `gridAdj` become nearest-neighbour steps of the torus.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

section Shell

variable {d m : ℕ} [NeZero m]

/-- The `k`-blocks outside `Z` adjacent to `Z` (index distance `≤ 1`). -/
def shellOut (Z : Set (Torus d m)) : Set (Torus d m) := {x | x ∉ Z ∧ ∃ y ∈ Z, supDist x y ≤ 1}

/-- Nearest-neighbour adjacency on the torus. -/
def torusAdj (x y : Torus d m) : Prop := ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ x = y + Pi.single μ 1

/-- The embedding of the grid `{0, …, s_i + 1}` around the box `box a s`: `u ↦ a + u - 1`. -/
def gridEmb (a : Torus d m) (u : Fin d → ℤ) : Torus d m := fun i => a i + ((u i - 1 : ℤ) : ZMod m)

theorem gridEmb_adj (a : Torus d m) {v w : Fin d → ℤ} (h : gridAdj v w) :
    torusAdj (gridEmb a v) (gridEmb a w) := by
  obtain ⟨i, ε, hε, rfl⟩ := h
  refine ⟨i, ?_⟩
  rcases hε with rfl | rfl
  · left
    funext j
    by_cases hj : j = i
    · subst hj; simp [gridEmb]; ring
    · simp [gridEmb, hj]
  · right
    funext j
    by_cases hj : j = i
    · subst hj; simp [gridEmb]; ring
    · simp [gridEmb, hj]

variable {a : Torus d m} {s : Fin d → ℕ}

theorem gridEmb_mem_shell (hs1 : ∀ i, 1 ≤ s i) (hsm : ∀ i, s i + 2 ≤ m) {u : Fin d → ℤ}
    (hu : u ∈ gridBd s) : gridEmb a u ∈ shellOut (box a s) := by
  obtain ⟨hub, i0, hi0⟩ := hu
  refine ⟨?_, ?_⟩
  · -- not in the box
    intro hx
    obtain ⟨j, hj, hji⟩ := hx i0
    have h1 : (((u i0 - 1 : ℤ)) : ZMod m) = (j : ZMod m) := by
      have := hji
      simp only [gridEmb] at this
      exact add_left_cancel this
    have h2 : ((u i0 - 1 - (j : ℤ) : ℤ) : ZMod m) = 0 := by
      rw [Int.cast_sub, h1]; simp
    have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp h2
    have hb := hub i0
    have hsm' := hsm i0
    have h4 : u i0 - 1 - (j : ℤ) = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd h3 ?_
      rw [abs_lt]; constructor <;> omega
    omega
  · -- adjacent to the box
    refine ⟨fun i => a i + ((Int.toNat (min (max (u i - 1) 0) ((s i : ℤ) - 1)) : ℕ) : ZMod m), ?_, ?_⟩
    · intro i
      refine ⟨Int.toNat (min (max (u i - 1) 0) ((s i : ℤ) - 1)), ?_, rfl⟩
      have := hs1 i
      omega
    · rw [supDist_le_iff]
      intro i
      rw [cycNorm_le_iff]
      refine ⟨u i - 1 - (Int.toNat (min (max (u i - 1) 0) ((s i : ℤ) - 1)) : ℤ), ?_, ?_⟩
      · have := hub i; have := hs1 i
        rw [abs_le]; constructor <;> omega
      · simp only [gridEmb]; push_cast; ring

theorem exists_gridEmb {x : Torus d m} (hx : x ∈ shellOut (box a s)) :
    ∃ u ∈ gridBd s, gridEmb a u = x := by
  obtain ⟨hxn, y, hy, hd⟩ := hx
  choose j hjs hjy using hy
  rw [supDist_le_iff] at hd
  have ht : ∀ i, ∃ t : ℤ, |t| ≤ 1 ∧ (t : ZMod m) = x i - y i := fun i =>
    (cycNorm_le_iff _ _).mp (hd i)
  choose t htabs htcast using ht
  set u : Fin d → ℤ := fun i => (j i : ℤ) + t i + 1 with hu
  have hxu : gridEmb a u = x := by
    funext i
    simp only [gridEmb, hu]
    have : (((j i : ℤ) + t i + 1 - 1 : ℤ) : ZMod m) = (j i : ZMod m) + (t i : ZMod m) := by
      push_cast; ring
    rw [this, htcast i, hjy i]; ring
  have hbox : u ∈ gridBox s := by
    intro i
    have := hjs i; have := htabs i
    rw [abs_le] at this
    simp only [hu]; constructor <;> omega
  refine ⟨u, ⟨hbox, ?_⟩, hxu⟩
  by_contra hcon
  push Not at hcon
  apply hxn
  intro i
  have h1 := hcon i
  have h2 := hbox i
  refine ⟨Int.toNat (u i - 1), by omega, ?_⟩
  rw [← hxu]
  simp only [gridEmb]
  congr 1
  have : ((Int.toNat (u i - 1) : ℕ) : ℤ) = u i - 1 := Int.toNat_of_nonneg (by omega)
  rw [← this]; simp

theorem gridEmb_image_eq (hs1 : ∀ i, 1 ≤ s i) (hsm : ∀ i, s i + 2 ≤ m) :
    gridEmb a '' gridBd s = shellOut (box a s) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩; exact gridEmb_mem_shell hs1 hsm hu
  · intro hx
    obtain ⟨u, hu, hux⟩ := exists_gridEmb hx
    exact ⟨u, hu, hux⟩

/-- Any two blocks of the layer of a box are joined inside the layer by at most `2 ∑ (s_i + 1)` nearest-neighbour steps. -/
theorem shell_reach (hd : 2 ≤ d) (hs1 : ∀ i, 1 ≤ s i) (hsm : ∀ i, s i + 2 ≤ m) {z z' : Torus d m}
    (hz : z ∈ shellOut (box a s)) (hz' : z' ∈ shellOut (box a s)) :
    ∃ n ≤ 2 * ∑ i, (s i + 1), ReachIn torusAdj (shellOut (box a s)) z z' n := by
  obtain ⟨u, hu, rfl⟩ := exists_gridEmb hz
  obtain ⟨v, hv, rfl⟩ := exists_gridEmb hz'
  obtain ⟨n, hn, h⟩ := boundary_reach hd hu hv
  refine ⟨n, hn, ?_⟩
  exact h.map (gridEmb a) (fun _ _ h => gridEmb_adj a h)
    (fun w hw => gridEmb_mem_shell hs1 hsm hw)

theorem reach_norm_le {E : Type*} [SeminormedAddCommGroup E] {Z : Set (Torus d m)} (ψ : Torus d m → E)
    {B : ℝ} (hB : ∀ x y, x ∈ shellOut Z → y ∈ shellOut Z → torusAdj x y → ‖ψ x - ψ y‖ ≤ B)
    {z z' : Torus d m} {n : ℕ} (h : ReachIn torusAdj (shellOut Z) z z' n) :
    ‖ψ z - ψ z'‖ ≤ n * B := by
  induction h with
  | refl hu => simp
  | @step v w n hr hw ha ih =>
    have hv := ReachIn.mem_right hr
    calc ‖ψ z - ψ w‖ = ‖(ψ z - ψ v) + (ψ v - ψ w)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖ψ z - ψ v‖ + ‖ψ v - ψ w‖ := norm_add_le _ _
      _ ≤ n * B + B := add_le_add ih (hB v w hv hw ha)
      _ = ((n + 1 : ℕ) : ℝ) * B := by push_cast; ring

end Shell

section RefVec

variable {d m N : ℕ} [NeZero m] [NeZero N]

/-- The finite set of blocks of the layer `∂(Z^c ∩ T_1^{(k)})`. -/
noncomputable def layerFinset (Z : Set (Torus d m)) : Finset (Torus d m) := by
  classical exact Finset.univ.filter (· ∈ shellOut Z)

theorem mem_layerFinset {Z : Set (Torus d m)} {x : Torus d m} : x ∈ layerFinset Z ↔ x ∈ shellOut Z := by
  classical simp [layerFinset]

/-- The mean `ψ̃ = |∂|⁻¹ ∑_{z ∈ ∂(Z^c)} ψ(z)` of a field over the layer (Definition III.3.4). -/
noncomputable def refMean (ψ : Torus d m → EuclideanSpace ℝ (Fin N)) (Z : Set (Torus d m)) :
    EuclideanSpace ℝ (Fin N) :=
  ((layerFinset Z).card : ℝ)⁻¹ • ∑ z ∈ layerFinset Z, ψ z

/-- **The reference vector** `ψ₀ = ψ̃ / |ψ̃|` (`:= e₁` if `ψ̃ = 0`) of Definition III.3.4, real fields. -/
noncomputable def refVec (ψ : Torus d m → EuclideanSpace ℝ (Fin N)) (Z : Set (Torus d m)) :
    EuclideanSpace ℝ (Fin N) :=
  if refMean ψ Z = 0 then EuclideanSpace.single (0 : Fin N) 1 else ‖refMean ψ Z‖⁻¹ • refMean ψ Z

theorem norm_refMean_sub_refVec (ψ : Torus d m → EuclideanSpace ℝ (Fin N)) (Z : Set (Torus d m)) :
    ‖refMean ψ Z - refVec ψ Z‖ = |‖refMean ψ Z‖ - 1| := by
  unfold refVec
  split_ifs with h
  · rw [h]; simp
  · have hn : 0 < ‖refMean ψ Z‖ := norm_pos_iff.mpr h
    have : refMean ψ Z - ‖refMean ψ Z‖⁻¹ • refMean ψ Z = (1 - ‖refMean ψ Z‖⁻¹) • refMean ψ Z := by
      rw [sub_smul, one_smul]
    rw [this, norm_smul, Real.norm_eq_abs]
    calc |1 - ‖refMean ψ Z‖⁻¹| * ‖refMean ψ Z‖ = |(1 - ‖refMean ψ Z‖⁻¹) * ‖refMean ψ Z‖| := by
          rw [abs_mul, abs_of_pos hn]
      _ = |‖refMean ψ Z‖ - 1| := by congr 1; field_simp

/-- **Lemma III.3.5 ((2.20)′)**: for a box `Z = box a s` of sides `≤ D` (in a torus of side `≥ D + 2`, `d ≥ 2`) and a
real field with `|∂ψ(b)| < 3δ` on the bonds of the layer and `||ψ(z)| - 1| < 3δ` on it,
`|ψ(z) - ψ₀| < (12 d (D + 2) + 3) δ` on the layer, `ψ₀ = refVec ψ Z`. -/
theorem refVec_close {D : ℕ} (hd : 2 ≤ d) (a : Torus d m) (s : Fin d → ℕ) (hs1 : ∀ i, 1 ≤ s i)
    (hsD : ∀ i, s i ≤ D) (hm : D + 2 ≤ m) (ψ : Torus d m → EuclideanSpace ℝ (Fin N)) {δ : ℝ}
    (hgrad : ∀ (x : Torus d m) (μ : Fin d), x ∈ shellOut (box a s) →
      x + Pi.single μ 1 ∈ shellOut (box a s) → ‖ψ (x + Pi.single μ 1) - ψ x‖ < 3 * δ)
    (hnorm : ∀ z ∈ shellOut (box a s), |‖ψ z‖ - 1| < 3 * δ) {z : Torus d m}
    (hz : z ∈ shellOut (box a s)) :
    ‖ψ z - refVec ψ (box a s)‖ < (12 * d * (D + 2) + 3) * δ := by
  have hsm : ∀ i, s i + 2 ≤ m := fun i => (Nat.add_le_add_right (hsD i) 2).trans hm
  set X := layerFinset (box a s) with hX
  have hzX : z ∈ X := mem_layerFinset.mpr hz
  have hcard : (0 : ℝ) < X.card := by exact_mod_cast Finset.card_pos.mpr ⟨z, hzX⟩
  have hδ : 0 < δ := by
    have := hnorm z hz; have := abs_nonneg (‖ψ z‖ - 1); linarith
  have hB : ∀ x y, x ∈ shellOut (box a s) → y ∈ shellOut (box a s) → torusAdj x y →
      ‖ψ x - ψ y‖ ≤ 3 * δ := by
    intro x y hx hy ⟨μ, h⟩
    rcases h with rfl | rfl
    · rw [norm_sub_rev]; exact (hgrad x μ hx hy).le
    · exact (hgrad y μ hy hx).le
  set C20 : ℝ := 6 * d * (D + 2) with hC20
  have hpair : ∀ z' ∈ X, ‖ψ z - ψ z'‖ ≤ C20 * δ := by
    intro z' hz'
    obtain ⟨n, hn, h⟩ := shell_reach hd hs1 hsm hz (mem_layerFinset.mp hz')
    have h1 := reach_norm_le ψ hB h
    have hsum : ∑ i : Fin d, (s i + 1) ≤ d * (D + 1) := by
      have : ∑ i : Fin d, (s i + 1) ≤ ∑ i : Fin d, (D + 1) :=
        Finset.sum_le_sum fun i _ => by have := hsD i; omega
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using this
    have hn' : (n : ℝ) ≤ 2 * (d * (D + 1)) := by
      have : n ≤ 2 * (d * (D + 1)) := by omega
      exact_mod_cast this
    calc ‖ψ z - ψ z'‖ ≤ n * (3 * δ) := h1
      _ ≤ 2 * (d * (D + 1)) * (3 * δ) := mul_le_mul_of_nonneg_right hn' (by positivity)
      _ ≤ C20 * δ := by rw [hC20]; nlinarith [hδ, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  -- distance to the mean
  have hmean : ‖ψ z - refMean ψ (box a s)‖ ≤ C20 * δ := by
    have e : ψ z - refMean ψ (box a s) = (X.card : ℝ)⁻¹ • ∑ z' ∈ X, (ψ z - ψ z') := by
      unfold refMean
      rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul,
        inv_mul_cancel₀ hcard.ne', one_smul]
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcard)]
    calc (X.card : ℝ)⁻¹ * ‖∑ z' ∈ X, (ψ z - ψ z')‖ ≤ (X.card : ℝ)⁻¹ * ∑ z' ∈ X, ‖ψ z - ψ z'‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hcard.le)
      _ ≤ (X.card : ℝ)⁻¹ * ∑ z' ∈ X, (C20 * δ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpair) (inv_nonneg.mpr hcard.le)
      _ = C20 * δ := by rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  -- the norm of the mean
  have hup : ‖refMean ψ (box a s)‖ < 1 + 3 * δ := by
    unfold refMean
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcard)]
    calc (X.card : ℝ)⁻¹ * ‖∑ z' ∈ X, ψ z'‖ ≤ (X.card : ℝ)⁻¹ * ∑ z' ∈ X, ‖ψ z'‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hcard.le)
      _ < (X.card : ℝ)⁻¹ * ∑ z' ∈ X, (1 + 3 * δ) := by
          refine mul_lt_mul_of_pos_left (Finset.sum_lt_sum_of_nonempty ⟨z, hzX⟩ fun z' hz' => ?_)
            (inv_pos.mpr hcard)
          have := hnorm z' (mem_layerFinset.mp hz')
          have := (abs_lt.mp this).2
          linarith
      _ = 1 + 3 * δ := by rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  have hlow : 1 - 3 * δ - C20 * δ < ‖refMean ψ (box a s)‖ := by
    have h1 := (abs_lt.mp (hnorm z hz)).1
    have h2 : ‖ψ z‖ ≤ ‖refMean ψ (box a s)‖ + ‖ψ z - refMean ψ (box a s)‖ := by
      calc ‖ψ z‖ = ‖refMean ψ (box a s) + (ψ z - refMean ψ (box a s))‖ := by rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith
  have hclose : |‖refMean ψ (box a s)‖ - 1| < (3 + C20) * δ := by
    have hC0 : 0 ≤ C20 * δ := by rw [hC20]; positivity
    rw [abs_lt]; constructor <;> nlinarith [(abs_lt.mp (hnorm z hz)).1, (abs_lt.mp (hnorm z hz)).2]
  calc ‖ψ z - refVec ψ (box a s)‖
      = ‖(ψ z - refMean ψ (box a s)) + (refMean ψ (box a s) - refVec ψ (box a s))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖ψ z - refMean ψ (box a s)‖ + ‖refMean ψ (box a s) - refVec ψ (box a s)‖ := norm_add_le _ _
    _ < C20 * δ + (3 + C20) * δ := by
        rw [norm_refMean_sub_refVec]
        exact add_lt_add_of_le_of_lt hmean hclose
    _ = (12 * d * (D + 2) + 3) * δ := by rw [hC20]; ring

/-- The complexified field `ℝ^N → ℂ^N`. -/
def toC (v : EuclideanSpace ℝ (Fin N)) : Fin N → ℂ := fun i => (v i : ℂ)

/-- The mean of a complex field over the layer. -/
noncomputable def refMeanC (ψ : Torus d m → (Fin N → ℂ)) (Z : Set (Torus d m)) : Fin N → ℂ :=
  (((layerFinset Z).card : ℂ))⁻¹ • ∑ z ∈ layerFinset Z, ψ z

/-- **The reference vector for complex fields** (Definition III.3.4): `ψ₀ = ψ̃ / (ψ̃·ψ̃)^{1/2}` with the principal
branch, `ψ₀ := e₁` if `ψ̃·ψ̃ ∈ (-∞, 0]`; `ψ̃·ψ̃ = ∑ ψ̃_i²` is the bilinear form. -/
noncomputable def refVecC (ψ : Torus d m → (Fin N → ℂ)) (Z : Set (Torus d m)) : Fin N → ℂ :=
  if (refMeanC ψ Z ⬝ᵥ refMeanC ψ Z).im = 0 ∧ (refMeanC ψ Z ⬝ᵥ refMeanC ψ Z).re ≤ 0 then Pi.single 0 1
  else ((refMeanC ψ Z ⬝ᵥ refMeanC ψ Z) ^ (1 / 2 : ℂ))⁻¹ • refMeanC ψ Z

theorem toC_dot (v : EuclideanSpace ℝ (Fin N)) : toC v ⬝ᵥ toC v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [toC, dotProduct, sq]

theorem refMeanC_toC (ψ : Torus d m → EuclideanSpace ℝ (Fin N)) (Z : Set (Torus d m)) :
    refMeanC (fun z => toC (ψ z)) Z = toC (refMean ψ Z) := by
  funext i
  simp [refMeanC, refMean, toC, Finset.sum_apply]

/-- On real fields the complex reference vector is the real one. -/
theorem refVecC_toC (ψ : Torus d m → EuclideanSpace ℝ (Fin N)) (Z : Set (Torus d m)) :
    refVecC (fun z => toC (ψ z)) Z = toC (refVec ψ Z) := by
  unfold refVecC refVec
  rw [refMeanC_toC, toC_dot]
  by_cases h : refMean ψ Z = 0
  · have : refMean ψ Z = 0 := h
    simp only [this, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.ofReal_zero,
      Complex.zero_re, Complex.zero_im, le_refl, and_self, ite_true]
    funext i
    by_cases hi : i = 0 <;> simp [toC, hi]
  · have hn : 0 < ‖refMean ψ Z‖ := norm_pos_iff.mpr h
    have hpos : 0 < ‖refMean ψ Z‖ ^ 2 := by positivity
    have hnot : ¬ ((((‖refMean ψ Z‖ ^ 2 : ℝ) : ℂ)).im = 0 ∧ (((‖refMean ψ Z‖ ^ 2 : ℝ) : ℂ)).re ≤ 0) := by
      rintro ⟨-, h2⟩
      rw [Complex.ofReal_re] at h2
      linarith
    have hsq : (((‖refMean ψ Z‖ ^ 2 : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = ((‖refMean ψ Z‖ : ℝ) : ℂ) := by
      have : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this, ← Complex.ofReal_cpow hpos.le]
      congr 1
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hn.le]
    simp only [hnot, h, ite_false, hsq]
    funext i
    simp [toC]

end RefVec

end Balaban.LargeField
