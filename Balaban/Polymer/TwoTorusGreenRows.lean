/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusCubeOps
public import Balaban.Localization.DecoupledLocal
import Mathlib.Tactic.LinearCombination

/-!
# The rows of the decoupled Green operator on two tori

For the whole-lattice generating set `levelGS j` of two step tori `CTorus d L N₁ m₁ K` and
`CTorus d L N₁' m₁ K`, identified on a centred box by `boxMap`, this file compares the rows of the
decoupled Green operator `G_s(A) = G*_s(A) (1 - 𝒦_s(A))⁻¹` on a set `T` of sites of the box such
that every interaction cube with a non-zero factor `s_z` lies inside `T` or avoids it (on both
tori).

* `Gstar_block`, `Kcal_block`: the block identities `P G*_s = G*_s P = ∑_{z inner} …` and
  `P 𝒦_s = 𝒦_s P = ∑_{z inner} …` for the indicator `P` of `T` (one torus).
* `Gstar_boxMap_apply`, `Kcal_boxMap_apply` (D1): the entries of `G*_s` and `𝒦_s` at two sites of
  `T` correspond, when the factors agree on the cubes inside `T` and the potentials agree on `T`.
* `resolvent_rows_transport`, `inv_one_sub_transport` (D2): an abstract block statement: the rows
  on `T` of `X (1 - K)⁻¹ f` and the entries of `(1 - K)⁻¹` on `T × T` correspond if those of `X` and
  `K` do and `K` does not couple `T` to its complement.
* `Gs_boxMap_rows`: the rows on `T` of `G_s(A) f` correspond.
* `decBg_green_rows_transport` (D3): the rows on a larger set `Y ⊇ T` correspond, when every active
  interaction cube meeting `Y` meets it inside `T` (both sides vanish on `Y \ T`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background Matrix

/-! ### Abstract block transport -/

section Abstract

variable {A B : Type*} [Fintype A] [Fintype B]

/-- A sum over a set `S`, transported by a map `ι` which is a bijection of `S` onto `S'`. -/
theorem sum_ite_transport (S : A → Prop) (S' : B → Prop) [DecidablePred S] [DecidablePred S']
    (ι : A → B) (hinj : ∀ a b, S a → S b → ι a = ι b → a = b) (hmap : ∀ a, S a → S' (ι a))
    (hsurj : ∀ b, S' b → ∃ a, S a ∧ ι a = b) (F : B → ℂ) :
    ∑ a : A, (if S a then F (ι a) else 0) = ∑ b : B, (if S' b then F b else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij (fun z _ => ι z) (fun z hz => ?_) (fun a ha b hb h => ?_)
    (fun z' hz' => ?_) (fun _ _ => rfl)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hmap z (Finset.mem_filter.1 hz).2⟩
  · exact hinj a b (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2 h
  · obtain ⟨a, ha, rfl⟩ := hsurj z' (Finset.mem_filter.1 hz').2
    exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩, rfl⟩

/-- **A row of a matrix-vector product, transported.**  If the terms of the row of `M u` at `x` and
of `M' u'` at `x'` vanish off `S` and `S'`, and correspond on `S` under `ι`, the rows agree. -/
theorem mulVec_apply_transport (S : A → Prop) (S' : B → Prop) [DecidablePred S] [DecidablePred S']
    (ι : A → B) (hinj : ∀ a b, S a → S b → ι a = ι b → a = b) (hmap : ∀ a, S a → S' (ι a))
    (hsurj : ∀ b, S' b → ∃ a, S a ∧ ι a = b) (M : Matrix A A ℂ) (M' : Matrix B B ℂ)
    (u : A → ℂ) (u' : B → ℂ) {x : A} {x' : B}
    (h0 : ∀ a, ¬ S a → M x a * u a = 0) (h0' : ∀ b, ¬ S' b → M' x' b * u' b = 0)
    (he : ∀ a, S a → M' x' (ι a) * u' (ι a) = M x a * u a) :
    (M' *ᵥ u') x' = (M *ᵥ u) x := by
  simp only [Matrix.mulVec, dotProduct]
  have h1 : ∑ a, M x a * u a = ∑ a, if S a then M' x' (ι a) * u' (ι a) else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : S a
    · rw [ite_eq_left ha, he a ha]
    · rw [ite_eq_right ha, h0 a ha]
  have h2 : ∑ b, M' x' b * u' b = ∑ b, if S' b then M' x' b * u' b else 0 := by
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : S' b
    · rw [ite_eq_left hb]
    · rw [ite_eq_right hb, h0' b hb]
  rw [h1, h2, sum_ite_transport S S' ι hinj hmap hsurj (fun b => M' x' b * u' b)]

/-- **An entry of a product, transported.** -/
theorem mul_apply_transport (S : A → Prop) (S' : B → Prop) [DecidablePred S] [DecidablePred S']
    (ι : A → B) (hinj : ∀ a b, S a → S b → ι a = ι b → a = b) (hmap : ∀ a, S a → S' (ι a))
    (hsurj : ∀ b, S' b → ∃ a, S a ∧ ι a = b) (M N : Matrix A A ℂ) (M' N' : Matrix B B ℂ)
    {x z : A} {x' z' : B}
    (h0 : ∀ a, ¬ S a → M x a * N a z = 0) (h0' : ∀ b, ¬ S' b → M' x' b * N' b z' = 0)
    (he : ∀ a, S a → M' x' (ι a) * N' (ι a) z' = M x a * N a z) :
    (M' * N') x' z' = (M * N) x z := by
  have e1 : (M * N) x z = (M *ᵥ fun a => N a z) x := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have e2 : (M' * N') x' z' = (M' *ᵥ fun b => N' b z') x' := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [e1, e2]
  exact mulVec_apply_transport S S' ι hinj hmap hsurj M M' _ _ h0 h0' he

/-- **D2 (abstract form): rows of `X (1 - K)⁻¹ f` on a block.**  Let `ι` be a bijection of `S ⊆ A`
onto `S' ⊆ B`.  Suppose the rows in `S` of `X` and `K` (and of `X'`, `K'`) only read columns in
`S`, the rows of `K'` off `S'` do not read columns in `S'`, the entries of `X`, `K` on `S × S`
correspond to those of `X'`, `K'`, `1 - K` and `1 - K'` are invertible and the sources correspond
on `S`.  Then the rows on `S` of `X (1 - K)⁻¹ f` and `X' (1 - K')⁻¹ f'` correspond. -/
theorem resolvent_rows_transport (S : A → Prop) (S' : B → Prop) [DecidablePred S]
    [DecidablePred S'] [DecidableEq A] [DecidableEq B]
    (ι : A → B) (hinj : ∀ a b, S a → S b → ι a = ι b → a = b) (hmap : ∀ a, S a → S' (ι a))
    (hsurj : ∀ b, S' b → ∃ a, S a ∧ ι a = b) (X Kc : Matrix A A ℂ) (X' Kc' : Matrix B B ℂ)
    (hX0 : ∀ x z, S x → ¬ S z → X x z = 0) (hK0 : ∀ x z, S x → ¬ S z → Kc x z = 0)
    (hX0' : ∀ x z, S' x → ¬ S' z → X' x z = 0) (hK0' : ∀ x z, S' x → ¬ S' z → Kc' x z = 0)
    (hKc' : ∀ x z, ¬ S' x → S' z → Kc' x z = 0)
    (hX : ∀ x z, S x → S z → X' (ι x) (ι z) = X x z)
    (hK : ∀ x z, S x → S z → Kc' (ι x) (ι z) = Kc x z)
    (hU : IsUnit (1 - Kc)) (hU' : IsUnit (1 - Kc'))
    {f : A → ℂ} {f' : B → ℂ} (hf : ∀ z, S z → f' (ι z) = f z) {y : A} (hy : S y) :
    ((X' * (1 - Kc')⁻¹) *ᵥ f') (ι y) = ((X * (1 - Kc)⁻¹) *ᵥ f) y := by
  obtain ⟨g, hg⟩ : ∃ g : A → ℂ, g = (1 - Kc)⁻¹ *ᵥ f := ⟨_, rfl⟩
  obtain ⟨g', hg'⟩ : ∃ g' : B → ℂ, g' = (1 - Kc')⁻¹ *ᵥ f' := ⟨_, rfl⟩
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hdet' := (Matrix.isUnit_iff_isUnit_det _).1 hU'
  have hgf : ∀ x, g x - (Kc *ᵥ g) x = f x := by
    have h1 : (1 - Kc) *ᵥ g = f := by
      rw [hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h1
    exact fun x => congrFun h1 x
  have hgf' : ∀ x, g' x - (Kc' *ᵥ g') x = f' x := by
    have h1 : (1 - Kc') *ᵥ g' = f' := by
      rw [hg', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet', Matrix.one_mulVec]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h1
    exact fun x => congrFun h1 x
  -- a left inverse of `ι` on `S`
  obtain ⟨κ, hκ⟩ : ∃ κ : B → A, ∀ a, S a → κ (ι a) = a := by
    refine ⟨fun b => if h : ∃ a, S a ∧ ι a = b then h.choose else y, fun a ha => ?_⟩
    have h : ∃ a', S a' ∧ ι a' = ι a := ⟨a, ha, rfl⟩
    dsimp only
    rw [dite_eq_left h]
    exact hinj _ _ h.choose_spec.1 ha h.choose_spec.2
  -- the difference of the transported solution and the second solution, on `S'`
  obtain ⟨v, hv⟩ : ∃ v : B → ℂ, v = fun b => if S' b then g (κ b) - g' b else 0 := ⟨_, rfl⟩
  have hvι : ∀ a, S a → v (ι a) = g a - g' (ι a) := fun a ha => by
    rw [hv]; dsimp only; rw [ite_eq_left (hmap a ha), hκ a ha]
  have hv0 : ∀ b, ¬ S' b → v b = 0 := fun b hb => by
    rw [hv]; dsimp only; rw [ite_eq_right hb]
  have hKg' : ∀ x, S x → (Kc' *ᵥ g') (ι x) = (Kc *ᵥ fun a => g' (ι a)) x := by
    intro x hx
    refine mulVec_apply_transport S S' ι hinj hmap hsurj Kc Kc' _ _ (fun a ha => ?_)
      (fun b hb => ?_) (fun a ha => ?_)
    · rw [hK0 x a hx ha, zero_mul]
    · rw [hK0' (ι x) b (hmap x hx) hb, zero_mul]
    · rw [hK x a hx ha]
  have hKv : ∀ x, S x → (Kc' *ᵥ v) (ι x) = (Kc *ᵥ g) x - (Kc' *ᵥ g') (ι x) := by
    intro x hx
    have e1 : (Kc' *ᵥ v) (ι x) = (Kc *ᵥ (g - fun a => g' (ι a))) x := by
      refine mulVec_apply_transport S S' ι hinj hmap hsurj Kc Kc' _ _ (fun a ha => ?_)
        (fun b hb => ?_) (fun a ha => ?_)
      · rw [hK0 x a hx ha, zero_mul]
      · rw [hv0 b hb, mul_zero]
      · rw [hK x a hx ha, hvι a ha]; rfl
    rw [e1, Matrix.mulVec_sub, Pi.sub_apply, hKg' x hx]
  have hv1 : (1 - Kc') *ᵥ v = 0 := by
    funext b
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.zero_apply]
    by_cases hb : S' b
    · obtain ⟨x, hx, rfl⟩ := hsurj b hb
      rw [hvι x hx, hKv x hx]
      linear_combination hgf x - hgf' (ι x) - hf x hx
    · rw [hv0 b hb, zero_sub, neg_eq_zero]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun b' _ => ?_
      by_cases hb' : S' b'
      · rw [hKc' b b' hb hb', zero_mul]
      · rw [hv0 b' hb', mul_zero]
  have hvz : v = 0 := by
    apply Matrix.mulVec_injective_iff_isUnit.2 hU'
    rw [hv1, Matrix.mulVec_zero]
  have hgg : ∀ a, S a → g' (ι a) = g a := fun a ha => by
    have := hvι a ha
    rw [hvz, Pi.zero_apply] at this
    exact (sub_eq_zero.1 this.symm).symm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hg, ← hg']
  refine mulVec_apply_transport S S' ι hinj hmap hsurj X X' g g' (fun a ha => ?_)
    (fun b hb => ?_) (fun a ha => ?_)
  · rw [hX0 y a hy ha, zero_mul]
  · rw [hX0' (ι y) b (hmap y hy) hb, zero_mul]
  · rw [hX y a hy ha, hgg a ha]

/-- **D2 (abstract form): the entries of `(1 - K)⁻¹` on a block.**  Under the hypotheses of
`resolvent_rows_transport` on `K`, the entries of `(1 - K)⁻¹` and `(1 - K')⁻¹` on `S × S`
correspond. -/
theorem inv_one_sub_transport (S : A → Prop) (S' : B → Prop) [DecidablePred S]
    [DecidablePred S'] [DecidableEq A] [DecidableEq B]
    (ι : A → B) (hinj : ∀ a b, S a → S b → ι a = ι b → a = b) (hmap : ∀ a, S a → S' (ι a))
    (hsurj : ∀ b, S' b → ∃ a, S a ∧ ι a = b) (Kc : Matrix A A ℂ) (Kc' : Matrix B B ℂ)
    (hK0 : ∀ x z, S x → ¬ S z → Kc x z = 0) (hK0' : ∀ x z, S' x → ¬ S' z → Kc' x z = 0)
    (hKc' : ∀ x z, ¬ S' x → S' z → Kc' x z = 0)
    (hK : ∀ x z, S x → S z → Kc' (ι x) (ι z) = Kc x z)
    (hU : IsUnit (1 - Kc)) (hU' : IsUnit (1 - Kc')) {x z : A} (hx : S x) (hz : S z) :
    (1 - Kc')⁻¹ (ι x) (ι z) = (1 - Kc)⁻¹ x z := by
  have h1 : ∀ x z, S x → ¬ S z → (1 : Matrix A A ℂ) x z = 0 := fun x z hx hz =>
    Matrix.one_apply_ne (fun h => hz (h ▸ hx))
  have h1' : ∀ x z, S' x → ¬ S' z → (1 : Matrix B B ℂ) x z = 0 := fun x z hx hz =>
    Matrix.one_apply_ne (fun h => hz (h ▸ hx))
  have hone : ∀ x z, S x → S z → (1 : Matrix B B ℂ) (ι x) (ι z) = (1 : Matrix A A ℂ) x z := by
    intro x z hx hz
    by_cases h : x = z
    · subst h; simp
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne fun h' => h (hinj x z hx hz h')]
  have hf : ∀ w, S w → (Pi.single (ι z) 1 : B → ℂ) (ι w) = (Pi.single z 1 : A → ℂ) w := by
    intro w hw
    by_cases h : w = z
    · subst h; simp
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne fun h' => h (hinj w z hw hz h')]
  have key := resolvent_rows_transport S S' ι hinj hmap hsurj 1 Kc 1 Kc' h1 hK0 h1' hK0' hKc'
    hone hK hU hU' hf hx
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using key

end Abstract

/-! ### The block identities on one torus -/

section Block

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ}

theorem indY_mul_apply (Y : Finset (CTorus d L N₁ m₁ K)) (M : Matrix (G.Ω 1) (G.Ω 1) ℂ)
    (x z : G.Ω 1) :
    (indY G Y * M) x z = if (x : CTorus d L N₁ m₁ K) ∈ Y then M x z else 0 := by
  unfold indY
  rw [Matrix.diagonal_mul]
  split_ifs <;> simp

theorem mul_indY_apply (Y : Finset (CTorus d L N₁ m₁ K)) (M : Matrix (G.Ω 1) (G.Ω 1) ℂ)
    (x z : G.Ω 1) :
    (M * indY G Y) x z = if (z : CTorus d L N₁ m₁ K) ∈ Y then M x z else 0 := by
  unfold indY
  rw [Matrix.mul_diagonal]
  split_ifs <;> simp

/-- **The block identity for `G*_s`.**  If every interaction cube with a non-zero factor lies inside
`T` or avoids it, then `P G*_s = G*_s P = ∑_{z inner} s_z χ_z G^{(z)} c_z`, `P` the indicator of
`T` and the sum over the centres whose interaction cube lies in `T`. -/
theorem Gstar_block (S : DGSetting G a ν) (hα : AdmPot G α) {T : Finset (CTorus d L N₁ m₁ K)}
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T) :
    indY G T * Gstar G a ν α s =
        ∑ q ∈ innerCentres G T, sProd G s q • (chiD G q * cubeG G a ν α q) ∧
      Gstar G a ν α s * indY G T =
        ∑ q ∈ innerCentres G T, sProd G s q • (chiD G q * cubeG G a ν α q) := by
  have hM : ∀ q ∈ cubeIdx G, RowSupp (chiD G q * cubeG G a ν α q) (intBox q) ∧
      chiD G q * cubeG G a ν α q * cD G q = chiD G q * cubeG G a ν α q := fun q hq =>
    ⟨rowSupp_chi_cubeG S hα hq, by rw [Matrix.mul_assoc, cubeG_mul_cD]⟩
  obtain ⟨hin, hout⟩ := blk_conditions (s := s) _ hM hdich
  exact sum_block_facts _ hin hout

/-- **The block identity for `𝒦_s`**: `P 𝒦_s = 𝒦_s P = ∑_{z inner} s_z K_z G^{(z)} c_z`. -/
theorem Kcal_block (S : DGSetting G a ν) {T : Finset (CTorus d L N₁ m₁ K)}
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T) :
    indY G T * Kcal G a ν α s =
        ∑ q ∈ innerCentres G T, sProd G s q • (Kz G a ν q * cubeG G a ν α q) ∧
      Kcal G a ν α s * indY G T =
        ∑ q ∈ innerCentres G T, sProd G s q • (Kz G a ν q * cubeG G a ν α q) := by
  have hM : ∀ q ∈ cubeIdx G, RowSupp (Kz G a ν q * cubeG G a ν α q) (intBox q) ∧
      Kz G a ν q * cubeG G a ν α q * cD G q = Kz G a ν q * cubeG G a ν α q := fun q hq =>
    ⟨rowSupp_Kz_cubeG S hq, by rw [Matrix.mul_assoc, cubeG_mul_cD]⟩
  obtain ⟨hin, hout⟩ := blk_conditions (s := s) _ hM hdich
  exact sum_block_facts _ hin hout

/-- `𝒦_s` commutes with the indicator of `T`. -/
theorem indY_mul_Kcal_comm (S : DGSetting G a ν) {T : Finset (CTorus d L N₁ m₁ K)}
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T) :
    indY G T * Kcal G a ν α s = Kcal G a ν α s * indY G T := by
  obtain ⟨h1, h2⟩ := Kcal_block (α := α) S hdich
  rw [h1, h2]

/-- `G*_s` commutes with the indicator of `T`. -/
theorem indY_mul_Gstar_comm (S : DGSetting G a ν) (hα : AdmPot G α)
    {T : Finset (CTorus d L N₁ m₁ K)} {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T) :
    indY G T * Gstar G a ν α s = Gstar G a ν α s * indY G T := by
  obtain ⟨h1, h2⟩ := Gstar_block S hα hdich
  rw [h1, h2]

theorem Kcal_apply_eq_zero_of_mem (S : DGSetting G a ν) {T : Finset (CTorus d L N₁ m₁ K)}
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    {x z : G.Ω 1} (hx : (x : CTorus d L N₁ m₁ K) ∈ T) (hz : (z : CTorus d L N₁ m₁ K) ∉ T) :
    Kcal G a ν α s x z = 0 := by
  have h := congrFun (congrFun (indY_mul_Kcal_comm (α := α) S hdich) x) z
  rw [indY_mul_apply, mul_indY_apply, ite_eq_left hx, ite_eq_right hz] at h
  exact h

theorem Kcal_apply_eq_zero_of_not_mem (S : DGSetting G a ν) {T : Finset (CTorus d L N₁ m₁ K)}
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    {x z : G.Ω 1} (hx : (x : CTorus d L N₁ m₁ K) ∉ T) (hz : (z : CTorus d L N₁ m₁ K) ∈ T) :
    Kcal G a ν α s x z = 0 := by
  have h := congrFun (congrFun (indY_mul_Kcal_comm (α := α) S hdich) x) z
  rw [indY_mul_apply, mul_indY_apply, ite_eq_right hx, ite_eq_left hz] at h
  exact h.symm

theorem Gstar_apply_eq_zero_of_mem (S : DGSetting G a ν) (hα : AdmPot G α)
    {T : Finset (CTorus d L N₁ m₁ K)} {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    {x z : G.Ω 1} (hx : (x : CTorus d L N₁ m₁ K) ∈ T) (hz : (z : CTorus d L N₁ m₁ K) ∉ T) :
    Gstar G a ν α s x z = 0 := by
  have h := congrFun (congrFun (indY_mul_Gstar_comm S hα hdich) x) z
  rw [indY_mul_apply, mul_indY_apply, ite_eq_left hx, ite_eq_right hz] at h
  exact h

/-- The row at a site of `T` of `G*_s` is the sum over the cubes inside `T`. -/
theorem Gstar_apply_of_mem (S : DGSetting G a ν) (hα : AdmPot G α)
    {T : Finset (CTorus d L N₁ m₁ K)} {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    {x : G.Ω 1} (hx : (x : CTorus d L N₁ m₁ K) ∈ T) (z : G.Ω 1) :
    Gstar G a ν α s x z =
      ∑ q ∈ innerCentres G T, sProd G s q * (chiD G q * cubeG G a ν α q) x z := by
  have h := congrFun (congrFun (Gstar_block S hα hdich).1 x) z
  rw [indY_mul_apply, ite_eq_left hx, Matrix.sum_apply] at h
  rw [h]
  simp only [Matrix.smul_apply, smul_eq_mul]

/-- The row at a site of `T` of `𝒦_s` is the sum over the cubes inside `T`. -/
theorem Kcal_apply_of_mem (S : DGSetting G a ν) {T : Finset (CTorus d L N₁ m₁ K)}
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    {x : G.Ω 1} (hx : (x : CTorus d L N₁ m₁ K) ∈ T) (z : G.Ω 1) :
    Kcal G a ν α s x z =
      ∑ q ∈ innerCentres G T, sProd G s q * (Kz G a ν q * cubeG G a ν α q) x z := by
  have h := congrFun (congrFun (Kcal_block (α := α) S hdich).1 x) z
  rw [indY_mul_apply, ite_eq_left hx, Matrix.sum_apply] at h
  rw [h]
  simp only [Matrix.smul_apply, smul_eq_mul]

/-- **Rows of `G_s(A) f` outside `T`.**  If every active interaction cube meets `Y` only inside
`T`, the rows of `G_s(A) f` on `Y \ T` vanish. -/
theorem Gs_apply_eq_zero_of_not_mem (S : DGSetting G a ν) (hα : AdmPot G α)
    {Y T : Finset (CTorus d L N₁ m₁ K)} {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hrow : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (f : G.Ω 1 → ℂ) {y : G.Ω 1} (hyY : (y : CTorus d L N₁ m₁ K) ∈ Y)
    (hyT : (y : CTorus d L N₁ m₁ K) ∉ T) : (Gs G a ν α s *ᵥ f) y = 0 := by
  unfold Gs Gstar
  rw [← Matrix.mulVec_mulVec, Matrix.sum_mulVec, Finset.sum_apply]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  by_cases hs : sProd G s q = 0
  · rw [hs, zero_mul]
  · have hyq : (y : CTorus d L N₁ m₁ K) ∉ intBox q := fun h => hyT (hrow q hq hs _ hyY h)
    rw [rowSupp_chi_cubeG S hα hq _ y hyq, mul_zero]

end Block

/-! ### The cubes inside `T` on two tori -/

/-- The base point of a centre lies in its interaction cube. -/
theorem base_mem_intBox {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]
    (q : ℕ × CTorus d L N₁ m₁ K) : q.2 ∈ intBox q := by
  rw [mem_intBox]
  intro μ
  refine ⟨0, ?_⟩
  have hB : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  simp only [Int.cast_zero, zero_mul, add_zero]
  rw [abs_lt]
  constructor <;> nlinarith

section Rows

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {j : ℕ}
variable (hj1 : 1 ≤ j) (hj : j ≤ K)

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ K) ((N₁ * L ^ m₁) * L ^ K)
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj

include hj1 in
/-- A centre of `levelGS j` whose interaction cube lies in `T` has its base point in `T`. -/
theorem inner_base_mem {T : Finset (CTorus d L N₁ m₁ K)} {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ innerCentres GA T) :
    ∃ y0, q = (j, y0) ∧ CubeBase (K := K) m₁ j y0 ∧ y0 ∈ T ∧ ∀ x ∈ intBox q, x ∈ T := by
  obtain ⟨hqc, hsub⟩ := Finset.mem_filter.1 hq
  obtain ⟨y0, rfl, hb⟩ := exists_of_mem_cubeIdx hj hqc
  have hall : ∀ x ∈ intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K), x ∈ T := fun x hx =>
    hsub ⟨x, levelGS_mem_Ω_one hj1 hj x⟩ hx
  exact ⟨y0, rfl, hb, hall _ (base_mem_intBox _), hall⟩

include hj1 in
theorem mem_innerCentres_levelGS {T : Finset (CTorus d L N₁ m₁ K)} {y0 : CTorus d L N₁ m₁ K}
    (hb : CubeBase (K := K) m₁ j y0)
    (hsub : ∀ x ∈ intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K), x ∈ T) :
    ((j, y0) : ℕ × CTorus d L N₁ m₁ K) ∈ innerCentres GA T :=
  Finset.mem_filter.2 ⟨(mem_cubeIdx_levelGS hj _).2 ⟨rfl, hj1, hb⟩, fun _ hx => hsub _ hx⟩

include hj1 in
/-- **The cubes inside `T` correspond.**  For `T` in the box of radius `R` and `T' = bm '' T`, the
image of a centre of `levelGS j` whose interaction cube lies in `T` is a centre whose interaction
cube lies in `T'`.  Margin: `2 (R + 3 L^(j+m₁)) + 1 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem innerCentres_mapsTo {T : Finset (CTorus d L N₁ m₁ K)}
    {T' : Finset (CTorus d L N₁' m₁ K)} (hT' : T.image bm = T') {R : ℕ}
    (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 2 * (R + 3 * L ^ (j + m₁)) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (R + 3 * L ^ (j + m₁)) + 1 < (N₁' * L ^ m₁) * L ^ K)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ innerCentres GA T) :
    Prod.map id bm q ∈ innerCentres GB T' := by
  obtain ⟨y0, rfl, hb, hy0T, hsub⟩ := inner_base_mem hj1 hj hq
  have hy0 := hTR y0 hy0T
  refine mem_innerCentres_levelGS hj1 hj (cubeBase_boxMap hj hb) fun w hw => ?_
  have him := intBox_image (N₁' := N₁') hy0 hn hn'
  have hw' : w ∈ bm '' (↑(intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K)) :
      Set (CTorus d L N₁ m₁ K)) := by
    rw [him]; exact hw
  obtain ⟨x, hx, hxw⟩ := hw'
  rw [← hT', Finset.mem_image]
  exact ⟨x, hsub x hx, hxw⟩

include hj1 in
/-- **The sum over the cubes inside `T`, on two tori.** -/
theorem sum_innerCentres_boxMap {T : Finset (CTorus d L N₁ m₁ K)}
    {T' : Finset (CTorus d L N₁' m₁ K)} (hT' : T.image bm = T') {R : ℕ}
    (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 2 * (R + 3 * L ^ (j + m₁)) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (R + 3 * L ^ (j + m₁)) + 1 < (N₁' * L ^ m₁) * L ^ K)
    (F : ℕ × CTorus d L N₁ m₁ K → ℂ) (F' : ℕ × CTorus d L N₁' m₁ K → ℂ)
    (hF : ∀ q ∈ innerCentres GA T, F' (Prod.map id bm q) = F q) :
    ∑ q ∈ innerCentres GB T', F' q = ∑ q ∈ innerCentres GA T, F q := by
  symm
  refine Finset.sum_bij (fun q _ => Prod.map id bm q)
    (fun q hq => innerCentres_mapsTo hj1 hj hT' hTR hn hn' hq)
    (fun q1 hq1 q2 hq2 h => ?_) (fun q' hq' => ?_) (fun q hq => (hF q hq).symm)
  · obtain ⟨y1, rfl, -, hy1T, -⟩ := inner_base_mem hj1 hj hq1
    obtain ⟨y2, rfl, -, hy2T, -⟩ := inner_base_mem hj1 hj hq2
    have h2 : bm y1 = bm y2 := congrArg Prod.snd h
    rw [boxMap_inj (hm' := (by omega : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ K)) (hTR y1 hy1T)
      (hTR y2 hy2T) h2]
  · obtain ⟨y', rfl, hb', hy'T, hsub'⟩ := inner_base_mem (N₁ := N₁') hj1 hj hq'
    rw [← hT', Finset.mem_image] at hy'T
    obtain ⟨y0, hy0T, rfl⟩ := hy'T
    have hy0 := hTR y0 hy0T
    have hb0 : CubeBase (K := K) m₁ j y0 := by
      have := cubeBase_boxMap (N₁ := N₁') (N₁' := N₁) hj hb'
      rwa [boxMap_boxMap (by omega) hy0] at this
    refine ⟨(j, y0), mem_innerCentres_levelGS hj1 hj hb0 fun x hx => ?_, rfl⟩
    have hxb := inBox_of_mem_intBox hy0 hn hx
    have h1 : bm x ∈ intBox ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) :=
      (mem_intBox_boxMap_iff hy0 hn hn' hxb).1 hx
    have h2 := hsub' _ h1
    rw [← hT', Finset.mem_image] at h2
    obtain ⟨x2, hx2T, hx2⟩ := h2
    have hx2b : InBox d (R + 3 * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) x2 :=
      inBox_mono (by omega) (hTR x2 hx2T)
    rw [← boxMap_inj (hm' := hn') hx2b hxb hx2]
    exact hx2T

local notation "ιb" x:max => Subtype.mk (bm (x : CTorus d L N₁ m₁ K))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := K) (ϱ := ϱ) hj1 hj _)

include hj1 in
/-- **The cube Green function of a cube inside `T`, with potentials corresponding on `T` only.**
For a centre whose interaction cube lies in `T` (`T` in the box of radius `R`, `T' = bm '' T`), the
entries of `cubeG` at two sites of the box of radius `R + 3 L^(j+m₁)` correspond, for admissible
potentials with `α'(bm x) = α x` on `T` (`cubeG_boxMap` asks this on the whole box; the potential of
the second torus is replaced on the box by the transported one, which does not change `cubeG` by
`cubeG_congr`).  Margin: `4 R + 12 L^(j+m₁) + 3 L^K + 5 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem cubeG_boxMap_inner {a : ℕ → ℝ} {ν : ℝ} (SA : DGSetting GA a ν) (SB : DGSetting GB a ν)
    {T : Finset (CTorus d L N₁ m₁ K)} {T' : Finset (CTorus d L N₁' m₁ K)} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + m₁) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + m₁) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot GA α) (hαB : AdmPot GB α')
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ T → α' (ιb x) = α x)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ innerCentres GA T) (x z : (GA).Ω 1)
    (hx : InBox d (R + 3 * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K))
    (hz : InBox d (R + 3 * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) (z : CTorus d L N₁ m₁ K)) :
    cubeG GB a ν α' (Prod.map id bm q) (ιb x) (ιb z) = cubeG GA a ν α q x z := by
  have hq' := innerCentres_mapsTo hj1 hj hT' hTR (by omega) (by omega) hq
  obtain ⟨y0, rfl, -, hy0T, -⟩ := inner_base_mem hj1 hj hq
  have hy0 := hTR y0 hy0T
  have hqc : ((j, y0) : ℕ × CTorus d L N₁ m₁ K) ∈ cubeIdx GA := (Finset.mem_filter.1 hq).1
  have hspA : ∀ w : CTorus d L N₁ m₁ K, (GA).spacing w = (L : ℝ) ^ j := fun w => by
    unfold GeneratingSet.spacing; rw [layerIndex_levelGS hj1 hj]
  have hspB : ∀ w : CTorus d L N₁' m₁ K, (GB).spacing w = (L : ℝ) ^ j := fun w => by
    unfold GeneratingSet.spacing; rw [layerIndex_levelGS hj1 hj]
  -- the potential of the second torus, replaced on the box by the transported one
  obtain ⟨α'', hα''⟩ : ∃ α'' : (GB).Ω 1 → ℂ, α'' = fun w : (GB).Ω 1 =>
      if InBox d (R + 3 * L ^ (j + m₁)) ((N₁' * L ^ m₁) * L ^ K) (w : CTorus d L N₁' m₁ K) then
        α ⟨bm' (w : CTorus d L N₁' m₁ K), levelGS_mem_Ω_one hj1 hj _⟩ else α' w := ⟨_, rfl⟩
  have hα''B : AdmPot GB α'' := by
    intro w
    rw [hα'']
    dsimp only
    split_ifs with hw
    · have h1 := hαA ⟨bm' (w : CTorus d L N₁' m₁ K), levelGS_mem_Ω_one hj1 hj _⟩
      rw [hspA] at h1
      rw [hspB]
      exact h1
    · exact hαB w
  have hα''x : ∀ x : (GA).Ω 1, InBox d (R + 3 * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K)
      (x : CTorus d L N₁ m₁ K) → α'' (ιb x) = α x := by
    intro x hx
    have h1 : InBox d (R + 3 * L ^ (j + m₁)) ((N₁' * L ^ m₁) * L ^ K)
        (bm (x : CTorus d L N₁ m₁ K)) := inBox_boxMap (by omega) hx
    rw [hα'']
    dsimp only
    split_ifs
    congr 1
    exact Subtype.ext (boxMap_boxMap (by omega) hx)
  have hagree'' : ∀ w : (GB).Ω 1, (w : CTorus d L N₁' m₁ K) ∈
      intBox (Prod.map id bm ((j, y0) : ℕ × CTorus d L N₁ m₁ K)) → α' w = α'' w := by
    intro w hw
    have hwT : (w : CTorus d L N₁' m₁ K) ∈ T' := (Finset.mem_filter.1 hq').2 w hw
    rw [← hT', Finset.mem_image] at hwT
    obtain ⟨x, hxT, hxw⟩ := hwT
    have hw' : w = ιb (⟨x, levelGS_mem_Ω_one hj1 hj x⟩ : (GA).Ω 1) := Subtype.ext hxw.symm
    rw [hw', hα ⟨x, levelGS_mem_Ω_one hj1 hj x⟩ hxT,
      hα''x ⟨x, levelGS_mem_Ω_one hj1 hj x⟩ (inBox_mono (by omega) (hTR x hxT))]
  rw [cubeG_congr SB hαB hα''B (Finset.mem_filter.1 hq').1 hagree'']
  exact cubeG_boxMap (ρ₀ := R) hj1 hj SA SB hy0 hqc (by omega) (by omega) (by omega) (by omega)
    hαA hα''B hα''x x z hx hz

include hj1 in
/-- The entries of `χ_z G^{(z)} c_z` of a cube inside `T` at two sites of `T` correspond. -/
theorem chiD_cubeG_boxMap_inner {a : ℕ → ℝ} {ν : ℝ} (SA : DGSetting GA a ν)
    (SB : DGSetting GB a ν) {T : Finset (CTorus d L N₁ m₁ K)} {T' : Finset (CTorus d L N₁' m₁ K)}
    (hT' : T.image bm = T') {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + m₁) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + m₁) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot GA α) (hαB : AdmPot GB α')
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ T → α' (ιb x) = α x)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ innerCentres GA T) (x z : (GA).Ω 1)
    (hx : (x : CTorus d L N₁ m₁ K) ∈ T) (hz : (z : CTorus d L N₁ m₁ K) ∈ T) :
    (chiD GB (Prod.map id bm q) * cubeG GB a ν α' (Prod.map id bm q)) (ιb x) (ιb z) =
      (chiD GA q * cubeG GA a ν α q) x z := by
  have hxR := hTR _ hx
  have hzR := hTR _ hz
  unfold chiD
  rw [Matrix.diagonal_mul, Matrix.diagonal_mul, cubeG_boxMap_inner hj1 hj SA SB hT' hTR hn hn'
    hαA hαB hα hq x z (inBox_mono (by omega) hxR) (inBox_mono (by omega) hzR)]
  obtain ⟨y0, rfl, -, hy0T, -⟩ := inner_base_mem hj1 hj hq
  have hy0 := hTR y0 hy0T
  have hc := chi_boxMap (ϱ := ϱ) (N₁' := N₁') (ρ := R) hj1 hj (by omega) (by omega) hxR
    (inBox_mono (by omega) hy0)
  simp only [hc]

include hj1 in
/-- The entries of `K_z G^{(z)} c_z` of a cube inside `T` at two sites of `T` correspond. -/
theorem Kz_cubeG_boxMap_inner {a : ℕ → ℝ} {ν : ℝ} (SA : DGSetting GA a ν)
    (SB : DGSetting GB a ν) {T : Finset (CTorus d L N₁ m₁ K)} {T' : Finset (CTorus d L N₁' m₁ K)}
    (hT' : T.image bm = T') {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + m₁) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + m₁) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot GA α) (hαB : AdmPot GB α')
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ T → α' (ιb x) = α x)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ innerCentres GA T) (x z : (GA).Ω 1)
    (hx : (x : CTorus d L N₁ m₁ K) ∈ T) (hz : (z : CTorus d L N₁ m₁ K) ∈ T) :
    (Kz GB a ν (Prod.map id bm q) * cubeG GB a ν α' (Prod.map id bm q)) (ιb x) (ιb z) =
      (Kz GA a ν q * cubeG GA a ν α q) x z := by
  have hq' := innerCentres_mapsTo hj1 hj hT' hTR (by omega) (by omega) hq
  have hqc' := (Finset.mem_filter.1 hq').1
  have hqc := (Finset.mem_filter.1 hq).1
  have hxR := hTR _ hx
  have hzR := hTR _ hz
  have hn1 : 2 * (R + 3 * L ^ (j + m₁)) + 1 < (N₁ * L ^ m₁) * L ^ K := by omega
  have hn2 : 2 * (R + 3 * L ^ (j + m₁)) + 1 < (N₁' * L ^ m₁) * L ^ K := by omega
  obtain ⟨y0, rfl, -, hy0T, -⟩ := inner_base_mem hj1 hj hq
  have hy0 := hTR y0 hy0T
  refine mul_apply_transport
    (fun w : (GA).Ω 1 => (w : CTorus d L N₁ m₁ K) ∈ intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K))
    (fun w : (GB).Ω 1 => (w : CTorus d L N₁' m₁ K) ∈
      intBox (Prod.map id bm ((j, y0) : ℕ × CTorus d L N₁ m₁ K)))
    (fun w => ιb w) (fun w1 w2 h1 h2 h => ?_) (fun w hw => ?_) (fun w' hw' => ?_) _ _ _ _
    (fun w hw => ?_) (fun w' hw' => ?_) (fun w hw => ?_)
  · exact Subtype.ext (boxMap_inj (hm' := hn2) (inBox_of_mem_intBox hy0 hn1 h1)
      (inBox_of_mem_intBox hy0 hn1 h2) (congrArg Subtype.val h))
  · exact (mem_intBox_boxMap_iff hy0 hn1 hn2 (inBox_of_mem_intBox hy0 hn1 hw)).1 hw
  · have hw'' : (w' : CTorus d L N₁' m₁ K) ∈
        intBox (Prod.map id bm ((j, y0) : ℕ × CTorus d L N₁ m₁ K)) := hw'
    have hwT : (w' : CTorus d L N₁' m₁ K) ∈ T' := (Finset.mem_filter.1 hq').2 w' hw''
    rw [← hT', Finset.mem_image] at hwT
    obtain ⟨x2, hx2T, hx2⟩ := hwT
    refine ⟨⟨x2, levelGS_mem_Ω_one hj1 hj x2⟩, ?_, Subtype.ext hx2⟩
    show x2 ∈ intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K)
    rw [mem_intBox_boxMap_iff hy0 hn1 hn2 (inBox_mono (by omega) (hTR x2 hx2T)), hx2]
    exact hw''
  · have h1 := cubeG_supp SA hαA hqc (Pi.single z 1) w hw
    rw [cubeG_mulVec_single] at h1
    rw [h1, mul_zero]
  · have h1 := cubeG_supp SB hαB hqc' (Pi.single (ιb z) 1) w' hw'
    rw [cubeG_mulVec_single] at h1
    rw [h1, mul_zero]
  · have hwR := inBox_of_mem_intBox hy0 hn1 hw
    rw [Kz_boxMap (ρ := R + 3 * L ^ (j + m₁)) hj1 hj a ν (inBox_mono (by omega) hy0) (by omega)
      (by omega) (by omega) (by omega) x w (inBox_mono (by omega) hxR) hwR,
      cubeG_boxMap_inner hj1 hj SA SB hT' hTR hn hn' hαA hαB hα hq w z hwR
        (inBox_mono (by omega) hzR)]

include hj1 in
/-- **D1 (`G*_s`).**  Let every active interaction cube lie inside `T` or avoid it, on both tori
(`T` in the box of radius `R`, `T' = bm '' T`), the factors `s_z` agree on the cubes inside `T`
and the potentials on `T`.  Then the entries of `G*_s` at two sites of `T` correspond.  The block
identity used is `P G*_s = ∑_{z inner} s_z χ_z G^{(z)} c_z` (`Gstar_block`) on each torus, and the
inner centres correspond under `Prod.map id bm` (`sum_innerCentres_boxMap`).  Margin:
`4 R + 12 L^(j+m₁) + 3 L^K + 5 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem Gstar_boxMap_apply {a : ℕ → ℝ} {ν : ℝ} (SA : DGSetting GA a ν) (SB : DGSetting GB a ν)
    {T : Finset (CTorus d L N₁ m₁ K)} {T' : Finset (CTorus d L N₁' m₁ K)} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + m₁) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + m₁) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot GA α) (hαB : AdmPot GB α')
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ T → α' (ιb x) = α x)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {s' : ℕ × CTorus d L N₁' m₁ K → ℂ}
    (hdich : ∀ q ∈ cubeIdx GA, sProd GA s q ≠ 0 → SubI GA (intBox q) T ∨ DisjI GA (intBox q) T)
    (hdich' : ∀ q ∈ cubeIdx GB, sProd GB s' q ≠ 0 →
      SubI GB (intBox q) T' ∨ DisjI GB (intBox q) T')
    (hagree : ∀ q ∈ innerCentres GA T, sProd GB s' (Prod.map id bm q) = sProd GA s q)
    (x z : (GA).Ω 1) (hx : (x : CTorus d L N₁ m₁ K) ∈ T) (hz : (z : CTorus d L N₁ m₁ K) ∈ T) :
    Gstar GB a ν α' s' (ιb x) (ιb z) = Gstar GA a ν α s x z := by
  have hx' : ((ιb x : (GB).Ω 1) : CTorus d L N₁' m₁ K) ∈ T' := by
    rw [← hT']; exact Finset.mem_image_of_mem _ hx
  rw [Gstar_apply_of_mem SA hαA hdich hx, Gstar_apply_of_mem SB hαB hdich' hx']
  refine sum_innerCentres_boxMap hj1 hj hT' hTR (by omega) (by omega) _ _ fun q hq => ?_
  rw [hagree q hq, chiD_cubeG_boxMap_inner hj1 hj SA SB hT' hTR hn hn' hαA hαB hα hq x z hx hz]

include hj1 in
/-- **D1 (`𝒦_s`).**  Under the hypotheses of `Gstar_boxMap_apply`, the entries of `𝒦_s` at two
sites of `T` correspond (block identity `P 𝒦_s = ∑_{z inner} s_z K_z G^{(z)} c_z`, `Kcal_block`). -/
theorem Kcal_boxMap_apply {a : ℕ → ℝ} {ν : ℝ} (SA : DGSetting GA a ν) (SB : DGSetting GB a ν)
    {T : Finset (CTorus d L N₁ m₁ K)} {T' : Finset (CTorus d L N₁' m₁ K)} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + m₁) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + m₁) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot GA α) (hαB : AdmPot GB α')
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ T → α' (ιb x) = α x)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {s' : ℕ × CTorus d L N₁' m₁ K → ℂ}
    (hdich : ∀ q ∈ cubeIdx GA, sProd GA s q ≠ 0 → SubI GA (intBox q) T ∨ DisjI GA (intBox q) T)
    (hdich' : ∀ q ∈ cubeIdx GB, sProd GB s' q ≠ 0 →
      SubI GB (intBox q) T' ∨ DisjI GB (intBox q) T')
    (hagree : ∀ q ∈ innerCentres GA T, sProd GB s' (Prod.map id bm q) = sProd GA s q)
    (x z : (GA).Ω 1) (hx : (x : CTorus d L N₁ m₁ K) ∈ T) (hz : (z : CTorus d L N₁ m₁ K) ∈ T) :
    Kcal GB a ν α' s' (ιb x) (ιb z) = Kcal GA a ν α s x z := by
  have hx' : ((ιb x : (GB).Ω 1) : CTorus d L N₁' m₁ K) ∈ T' := by
    rw [← hT']; exact Finset.mem_image_of_mem _ hx
  rw [Kcal_apply_of_mem SA hdich hx, Kcal_apply_of_mem SB hdich' hx']
  refine sum_innerCentres_boxMap hj1 hj hT' hTR (by omega) (by omega) _ _ fun q hq => ?_
  rw [hagree q hq, Kz_cubeG_boxMap_inner hj1 hj SA SB hT' hTR hn hn' hαA hαB hα hq x z hx hz]

end Rows

end Balaban.Polymer.TwoTorusStep
