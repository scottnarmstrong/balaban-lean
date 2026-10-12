/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Equivariance
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Lattice-symmetry covariance of the background fields (BACKGROUND.md §7)

For a lattice symmetry `S : LatSymm G G' σ` (see `LatSymm`) and a datum `D` over `G`, the transported
datum `S.sym D = (Ψ ∘ σ⁻¹, h̃ ∘ σ⁻¹)` over `G'` has the background fields transported:

* `LatSymm.bgField_sym`: `bgField G' a ν (S.sym D) = S.fld (bgField G a ν D)`, where
  `S.fld φ = φ ∘ σ⁻¹` (`LatSymm.fld_apply`: `S.fld φ (σ x, i) = φ (x, i)`);
* `LatSymm.bgMult_sym`: `bgMult G' a ν (S.sym D) = S.mul (bgMult G a ν D)`;
* `LatSymm.bgFieldC_sym`: the same for `bgFieldC`, `bgMultC` and every `c₀`.

No domain condition is needed: the Euler–Lagrange system, its small solutions, the action and the
minimizers correspond bijectively.  For `G' = G` the hypothesis on `σ` is that it preserves the
paving (the blocks of the scales carrying a layer of `G`) and the domains `Ω_j`.
-/

@[expose] public section

namespace Balaban
section BlockLemmas
variable {ℓ c m : ℕ} [NeZero ℓ]

theorem blockCoord_add_of_dvd (hℓ : ℓ = c * m) (a t : ZMod ℓ) (ht : c ∣ t.val) :
    blockCoord c m (a + t) = blockCoord c m a + ((t.val / c : ℕ) : ZMod m) := by
  unfold blockCoord
  have key : (a.val + t.val) % ℓ / c = ((a.val + t.val) / c) % m := by
    have := Nat.mod_mul_right_div_self (a.val + t.val) c m
    rwa [← hℓ] at this
  rw [ZMod.val_add, key, ZMod.natCast_mod, Nat.add_div_of_dvd_left ht]
  push_cast
  rfl

theorem blockCoord_neg_one_sub (hc : 0 < c) (hℓ : ℓ = c * m) (a : ZMod ℓ) :
    blockCoord c m (-1 - a) = -1 - blockCoord c m a := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact absurd (by simpa [h] using hℓ) (NeZero.ne ℓ)
    · exact h
  have hv : (-1 - a : ZMod ℓ).val = ℓ - 1 - a.val := by
    have h1 : a.val < ℓ := ZMod.val_lt a
    have : (-1 - a : ZMod ℓ) = ((ℓ - 1 - a.val : ℕ) : ZMod ℓ) := by
      have : ((ℓ - 1 - a.val : ℕ) : ZMod ℓ) = ((ℓ : ℕ) : ZMod ℓ) - 1 - (a.val : ZMod ℓ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
      rw [this]; simp
    rw [this, ZMod.val_natCast_of_lt (by omega)]
  have hq : (ℓ - 1 - a.val) / c = m - 1 - a.val / c := by
    have h1 : a.val < c * m := hℓ ▸ ZMod.val_lt a
    obtain ⟨q', hq'⟩ : ∃ q', m = a.val / c + 1 + q' := by
      refine ⟨m - a.val / c - 1, ?_⟩
      have : a.val / c < m := by rwa [Nat.div_lt_iff_lt_mul hc, mul_comm]
      omega
    have hr := Nat.mod_lt a.val hc
    have hd := Nat.div_add_mod a.val c
    have e : m - 1 - a.val / c = q' := by omega
    rw [e]
    have gen : ∀ n : ℕ, n = c * m → (n - 1 - a.val) / c = q' := by
      intro n hn
      have hexp : c * m = c * (a.val / c) + c + c * q' := by rw [hq']; ring
      have h2 : q' * c = c * q' := mul_comm _ _
      have h3 : (q' + 1) * c = c * q' + c := by ring
      apply Nat.div_eq_of_lt_le
      · rw [hn, hexp]; omega
      · rw [hn, hexp]; omega
    exact gen ℓ hℓ
  unfold blockCoord
  rw [hv, hq]
  have : a.val / c < m := by
    have h1 : a.val < c * m := hℓ ▸ ZMod.val_lt a
    rwa [Nat.div_lt_iff_lt_mul hc, mul_comm]
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  simp

end BlockLemmas
end Balaban

namespace Balaban.Background
open Balaban.Multiscale Matrix Finset
variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The lattice structure of a symmetry of the torus**: a permutation `σ` of the fine torus which
maps the nearest-neighbour structure to itself, permuting the coordinate directions by `perm` and
reversing the orientation of exactly the directions `μ` with `flip μ` (the same orientation at
every site): `σ (x + e_μ) = σ x ± e_{perm μ}`. -/
structure NbrSymm (σ : Equiv.Perm (Torus d (N₀ * L ^ k))) where
  /-- The permutation of the coordinate directions. -/
  perm : Equiv.Perm (Fin d)
  /-- The directions whose orientation is reversed. -/
  flip : Fin d → Bool
  step : ∀ (x : Torus d (N₀ * L ^ k)) (μ : Fin d), σ (x + Pi.single μ 1) =
    if flip μ then σ x - Pi.single (perm μ) 1 else σ x + Pi.single (perm μ) 1

omit [NeZero N₀] [NeZero L] in
theorem NbrSymm.step_sub {σ : Equiv.Perm (Torus d (N₀ * L ^ k))} (S : NbrSymm σ)
    (x : Torus d (N₀ * L ^ k)) (μ : Fin d) : σ (x - Pi.single μ 1) =
    if S.flip μ then σ x + Pi.single (S.perm μ) 1 else σ x - Pi.single (S.perm μ) 1 := by
  have h := S.step (x - Pi.single μ 1) μ
  rw [sub_add_cancel] at h
  generalize σ (x - Pi.single μ 1) = A at h ⊢
  cases hf : S.flip μ <;> simp only [hf] at h ⊢ <;> simp at h ⊢ <;> rw [h] <;> abel

/-- **A symmetry of the paved torus up to scale `j`**: a lattice symmetry (`NbrSymm`) which maps
the `n`-blocks to `n`-blocks for `1 ≤ n ≤ j` (`n ≤ k`).  These are the Euclidean symmetries of the
torus that preserve the blocks of side `L ^ n`, `n ≤ j`: compositions of translations by multiples
of `L ^ j`, reflections `x_μ ↦ c - 1 - x_μ` (`L ^ j ∣ c`), and permutations of the coordinates
(`TorusSymm.ofTranslate`, `TorusSymm.ofReflect`, `TorusSymm.ofCoordPerm`, `TorusSymm.trans`). -/
structure TorusSymm (j : ℕ) (σ : Equiv.Perm (Torus d (N₀ * L ^ k))) extends NbrSymm σ where
  block : ∀ n, 1 ≤ n → n ≤ j → n ≤ k → ∀ x y,
    jBlock d L N₀ k n (σ x) = jBlock d L N₀ k n (σ y) ↔ jBlock d L N₀ k n x = jBlock d L N₀ k n y

/-- **A lattice symmetry from the generating set `G` to the generating set `G'`**: a lattice
symmetry of the torus (`NbrSymm`) which

* maps `Ω_j` onto `Ω'_j` for `1 ≤ j ≤ k + 1` (`omega`);
* maps the `n`-blocks to `n`-blocks for those scales `n` that carry a layer of `G` (`block`).

Symmetries of the paved torus up to scale `j` (`TorusSymm`) give lattice symmetries for the
generating sets whose layers have scales `≤ j` (`LatSymm.ofTorusSymm`). -/
structure LatSymm (G G' : GeneratingSet d L N₀ k ϱ) (σ : Equiv.Perm (Torus d (N₀ * L ^ k)))
    extends NbrSymm σ where
  omega : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ x, σ x ∈ G'.Ω j ↔ x ∈ G.Ω j
  block : ∀ n, 1 ≤ n → n ≤ k → (G.layer n).Nonempty → ∀ x y,
    jBlock d L N₀ k n (σ x) = jBlock d L N₀ k n (σ y) ↔ jBlock d L N₀ k n x = jBlock d L N₀ k n y

namespace LatSymm

variable {G G' : GeneratingSet d L N₀ k ϱ} {σ : Equiv.Perm (Torus d (N₀ * L ^ k))}
  (S : LatSymm G G' σ)

include S

theorem mem_Ω1 (x : Torus d (N₀ * L ^ k)) : σ x ∈ G'.Ω 1 ↔ x ∈ G.Ω 1 :=
  S.omega 1 le_rfl (by omega) x

theorem mem_layer {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) (x : Torus d (N₀ * L ^ k)) :
    σ x ∈ G'.layer j ↔ x ∈ G.layer j := by
  rw [GeneratingSet.mem_layer, GeneratingSet.mem_layer, S.omega j hj (by omega),
    S.omega (j + 1) (by omega) (by omega)]

theorem layerIndex_eq (x : Torus d (N₀ * L ^ k)) : G'.layerIndex (σ x) = G.layerIndex x := by
  by_cases hx : x ∈ G.Ω 1
  · obtain ⟨h1, hk, hl⟩ := G.layerIndex_spec hx
    exact G'.layerIndex_eq h1 hk ((S.mem_layer h1 hk x).2 hl)
  · rw [layerIndex_of_not_mem G hx, layerIndex_of_not_mem G' (fun h => hx ((S.mem_Ω1 x).1 h))]

theorem spacing_eq (x : Torus d (N₀ * L ^ k)) : G'.spacing (σ x) = G.spacing x := by
  simp [GeneratingSet.spacing, S.layerIndex_eq]

theorem blk_iff {n : ℕ} (h1 : 1 ≤ n) (hk : n ≤ k) (hne : (G.layer n).Nonempty)
    (x y : Torus d (N₀ * L ^ k)) :
    y ∈ G'.blk n (σ x) ↔ σ.symm y ∈ G.blk n x := by
  rw [GeneratingSet.mem_blk, GeneratingSet.mem_blk]
  simpa using S.block n h1 hk hne (σ.symm y) x

theorem adj_iff (x y : Torus d (N₀ * L ^ k)) : Adj (σ x) (σ y) ↔ Adj x y := by
  constructor
  · rintro ⟨ν, h | h⟩
    · obtain ⟨μ, rfl⟩ : ∃ μ, S.perm μ = ν := ⟨S.perm.symm ν, by simp⟩
      by_cases hf : S.flip μ
      · have := S.step_sub x μ
        simp only [hf, ↓reduceIte] at this
        have : y = x - Pi.single μ 1 := σ.injective (by rw [h, this])
        exact ⟨μ, Or.inr (by rw [this]; abel)⟩
      · have := S.step x μ
        simp only [hf, Bool.false_eq_true, ↓reduceIte] at this
        exact ⟨μ, Or.inl (σ.injective (by rw [h, this]))⟩
    · obtain ⟨μ, rfl⟩ : ∃ μ, S.perm μ = ν := ⟨S.perm.symm ν, by simp⟩
      by_cases hf : S.flip μ
      · have := S.step_sub y μ
        simp only [hf, ↓reduceIte] at this
        have : x = y - Pi.single μ 1 := σ.injective (by rw [h, this])
        exact ⟨μ, Or.inl (by rw [this]; abel)⟩
      · have := S.step y μ
        simp only [hf, Bool.false_eq_true, ↓reduceIte] at this
        exact ⟨μ, Or.inr (σ.injective (by rw [h, this]))⟩
  · rintro ⟨μ, h | h⟩
    · refine ⟨S.perm μ, ?_⟩
      have := S.step x μ
      rw [← h] at this
      by_cases hf : S.flip μ
      · simp only [hf, ↓reduceIte] at this
        right; rw [this]; abel
      · simp only [hf, Bool.false_eq_true, ↓reduceIte] at this
        left; exact this
    · refine ⟨S.perm μ, ?_⟩
      have := S.step y μ
      rw [← h] at this
      by_cases hf : S.flip μ
      · simp only [hf, ↓reduceIte] at this
        left; rw [this]; abel
      · simp only [hf, Bool.false_eq_true, ↓reduceIte] at this
        right; exact this

theorem mem_collar (x : Torus d (N₀ * L ^ k)) : σ x ∈ collar G' ↔ x ∈ collar G := by
  rw [Balaban.Background.mem_collar, Balaban.Background.mem_collar, S.mem_Ω1]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨y, hy, hadj⟩
    refine ⟨σ.symm y, (S.mem_Ω1 _).1 (by simpa using hy), ?_⟩
    rw [← S.adj_iff]; simpa using hadj
  · rintro ⟨y, hy, hadj⟩
    exact ⟨σ y, (S.mem_Ω1 _).2 hy, (S.adj_iff _ _).2 hadj⟩

theorem mem_dataSites (x : Torus d (N₀ * L ^ k)) : σ x ∈ dataSites G' ↔ x ∈ dataSites G := by
  rw [Balaban.Background.mem_dataSites, Balaban.Background.mem_dataSites, S.mem_Ω1, S.mem_collar]


/-- The bijection `Ω₁ → Ω₁'` induced by `σ`. -/
def Ω1Equiv : G.Ω 1 ≃ G'.Ω 1 := σ.subtypeEquiv (fun x => (S.mem_Ω1 x).symm)

@[simp] theorem coe_Ω1Equiv (x : G.Ω 1) : ((S.Ω1Equiv x : G'.Ω 1) : Torus d (N₀ * L ^ k)) = σ (x : Torus d (N₀ * L ^ k)) := rfl

/-- The transported datum `σ•D = (Ψ ∘ σ⁻¹, h ∘ σ⁻¹)`. -/
def sym {N : ℕ} (D : BgData G N) : BgData G' N where
  Ψ y := D.Ψ (σ.symm y)
  h y := D.h (σ.symm y)
  Ψ_layerConst := by
    intro n h1 hk y hy y' hy'
    obtain ⟨x, rfl⟩ := σ.surjective y
    obtain ⟨x', rfl⟩ := σ.surjective y'
    simp only [Equiv.symm_apply_apply]
    have hx := (S.mem_layer h1 hk x).1 hy
    have hx' := (S.blk_iff h1 hk ⟨x, hx⟩ x (σ x')).1 hy'
    simp only [Equiv.symm_apply_apply] at hx'
    exact D.Ψ_layerConst n h1 hk x hx x' hx'
  h_layerConst := by
    intro n h1 hk y hy y' hy'
    obtain ⟨x, rfl⟩ := σ.surjective y
    obtain ⟨x', rfl⟩ := σ.surjective y'
    simp only [Equiv.symm_apply_apply]
    have hx := (S.mem_layer h1 hk x).1 hy
    have hx' := (S.blk_iff h1 hk ⟨x, hx⟩ x (σ x')).1 hy'
    simp only [Equiv.symm_apply_apply] at hx'
    exact D.h_layerConst n h1 hk x hx x' hx'
  Ψ_zero := by
    intro y hy
    obtain ⟨x, rfl⟩ := σ.surjective y
    simp only [Equiv.symm_apply_apply]
    exact D.Ψ_zero x (fun h => hy ((S.mem_dataSites x).2 h))
  h_zero := by
    intro y hy
    obtain ⟨x, rfl⟩ := σ.surjective y
    simp only [Equiv.symm_apply_apply]
    exact D.h_zero x (fun h => hy ((S.mem_Ω1 x).2 h))

/-- The transported field `φ ∘ σ⁻¹` on `Ω₁'`. -/
def fld {N : ℕ} (φ : G.Ω 1 × Fin N → ℂ) : G'.Ω 1 × Fin N → ℂ :=
  fun p => φ (S.Ω1Equiv.symm p.1, p.2)

@[simp] theorem fld_apply {N : ℕ} (φ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) (i : Fin N) :
    S.fld φ (S.Ω1Equiv x, i) = φ (x, i) := by simp [fld]

/-- The field transport as an equivalence. -/
def fldEquiv {N : ℕ} : (G.Ω 1 × Fin N → ℂ) ≃ (G'.Ω 1 × Fin N → ℂ) where
  toFun := S.fld
  invFun := fun φ' p => φ' (S.Ω1Equiv p.1, p.2)
  left_inv := fun φ => by funext p; simp [fld]
  right_inv := fun φ' => by funext p; simp [fld]

/-- The transported multiplier `α ∘ σ⁻¹`. -/
def mul (α : G.Ω 1 → ℂ) : G'.Ω 1 → ℂ := fun y => α (S.Ω1Equiv.symm y)

@[simp] theorem mul_apply (α : G.Ω 1 → ℂ) (x : G.Ω 1) : S.mul α (S.Ω1Equiv x) = α x := by
  simp [mul]

/-- The transported datum is real iff the original is. -/
theorem isReal_sym {N : ℕ} {D : BgData G N} (h : D.IsReal) : (S.sym D).IsReal :=
  fun x i => h (σ.symm x) i

theorem bdry_swap {β : Type*} [AddCommMonoid β] (F : Torus d (N₀ * L ^ k) → β)
    (x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    F (σ x + Pi.single (S.perm μ) 1) + F (σ x - Pi.single (S.perm μ) 1) =
      F (σ (x + Pi.single μ 1)) + F (σ (x - Pi.single μ 1)) := by
  rw [S.step, S.step_sub]
  cases S.flip μ
  · simp
  · simp [add_comm]


theorem source_sym (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) (x : G.Ω 1) (i : Fin N) :
    source G' a ν (S.sym D) (S.Ω1Equiv x, i) = source G a ν D (x, i) := by
  simp only [source, qStar, boundaryTerm, coe_Ω1Equiv, S.layerIndex_eq, sym,
    Equiv.symm_apply_apply]
  congr 1
  rw [← Equiv.sum_comp S.perm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have := S.bdry_swap (fun z => if z ∈ collar G' then D.Ψ (σ.symm z) i else 0) x μ
  simp only [S.mem_collar, Equiv.symm_apply_apply] at this
  convert this using 2 <;> congr

omit S in
theorem lap_entry (ν : ℝ) (x y : Torus d (N₀ * L ^ k)) :
    latticeLaplacian d (N₀ * L ^ k) ν x y =
      (2 * d + ν) * (if x = y then 1 else 0) -
        ∑ μ : Fin d, ((if y = x + Pi.single μ 1 then (1 : ℝ) else 0) +
          (if x = y + Pi.single μ 1 then 1 else 0)) := by
  simp [latticeLaplacian, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.sum_apply, shiftMatrix, Matrix.transpose_apply]

theorem lap_sym (ν : ℝ) (x y : Torus d (N₀ * L ^ k)) :
    latticeLaplacian d (N₀ * L ^ k) ν (σ x) (σ y) = latticeLaplacian d (N₀ * L ^ k) ν x y := by
  rw [lap_entry, lap_entry]
  congr 1
  · simp
  · rw [← Equiv.sum_comp S.perm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have h1 := S.step x μ
    have h2 := S.step y μ
    have h3 := S.step_sub x μ
    have h4 := S.step_sub y μ
    cases hf : S.flip μ <;> simp only [hf, Bool.false_eq_true, ↓reduceIte] at h1 h2 h3 h4
    · simp only [← h1, ← h2, σ.apply_eq_iff_eq]
    · simp only [← h3, ← h4, σ.apply_eq_iff_eq]
      have e1 : y = x - Pi.single μ 1 ↔ x = y + Pi.single μ 1 := by
        rw [eq_sub_iff_add_eq, eq_comm]
      have e2 : x = y - Pi.single μ 1 ↔ y = x + Pi.single μ 1 := by
        rw [eq_sub_iff_add_eq, eq_comm]
      simp only [e1, e2]
      ring


theorem layerProj_sym {j : ℕ} (h1 : 1 ≤ j) (hk : j ≤ k) (x y : Torus d (N₀ * L ^ k)) :
    layerProjMatrix G' j (σ x) (σ y) = layerProjMatrix G j x y := by
  by_cases hxy : x ∈ G.layer j ∧ y ∈ G.layer j
  · have hb := S.block j h1 hk ⟨x, hxy.1⟩ x y
    simp only [jBlock] at hb
    simp only [layerProjMatrix, blockProjMatrix, S.mem_layer h1 hk, hb]
  · simp [layerProjMatrix, S.mem_layer h1 hk, hxy]

theorem avg_sym (a : ℕ → ℝ) (x y : Torus d (N₀ * L ^ k)) :
    avgMatrix G' a (σ x) (σ y) = avgMatrix G a x y := by
  simp only [avgMatrix, Matrix.sum_apply, Matrix.smul_apply]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨h1, hk⟩ := Finset.mem_Icc.1 hj
  rw [S.layerProj_sym h1 hk]

theorem full_sym (a : ℕ → ℝ) (ν : ℝ) (x y : Torus d (N₀ * L ^ k)) :
    fullMatrix G' a ν (σ x) (σ y) = fullMatrix G a ν x y := by
  simp only [fullMatrix, Matrix.add_apply, S.lap_sym, S.avg_sym]

theorem dirichlet_sym (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) (x y : G.Ω 1) :
    dirichletOperator G' a ν (S.mul α) (S.Ω1Equiv x) (S.Ω1Equiv y) = dirichletOperator G a ν α x y := by
  simp only [dirichletOperator, Matrix.add_apply, Green.restrictOp, Matrix.submatrix_apply,
    Matrix.diagonal_apply, Matrix.map_apply, coe_Ω1Equiv, S.full_sym, mul_apply,
    Equiv.apply_eq_iff_eq]

theorem liftOp_sym (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) (φ : G.Ω 1 × Fin N → ℂ)
    (x : G.Ω 1) (i : Fin N) :
    (liftOp N (dirichletOperator G' a ν (S.mul α)) *ᵥ S.fld φ) (S.Ω1Equiv x, i) =
      (liftOp N (dirichletOperator G a ν α) *ᵥ φ) (x, i) := by
  rw [liftOp_mulVec, liftOp_mulVec]
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp S.Ω1Equiv]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [S.dirichlet_sym, S.fld_apply]


theorem isEL_sym_iff (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ)
    (α : G.Ω 1 → ℂ) :
    IsEL G' a ν (S.sym D) (S.fld φ) (S.mul α) ↔ IsEL G a ν D φ α := by
  unfold IsEL
  refine and_congr ⟨fun h => ?_, fun h => ?_⟩ ⟨fun h x => ?_, fun h y => ?_⟩
  · funext ⟨x, i⟩
    have := congrFun h (S.Ω1Equiv x, i)
    rwa [S.liftOp_sym, S.source_sym] at this
  · funext ⟨y, i⟩
    obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
    rw [S.liftOp_sym, S.source_sym]
    exact congrFun h (x, i)
  · have := h (S.Ω1Equiv x)
    simpa using this
  · obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
    simpa using h x

theorem isSmallSolution_sym_iff (a : ℕ → ℝ) (ν c₀ : ℝ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ)
    (α : G.Ω 1 → ℂ) :
    IsSmallSolution G' a ν c₀ (S.sym D) (S.fld φ) (S.mul α) ↔ IsSmallSolution G a ν c₀ D φ α := by
  unfold IsSmallSolution
  refine and_congr (S.isEL_sym_iff a ν D φ α) ⟨fun h x => ?_, fun h y => ?_⟩
  · have := h (S.Ω1Equiv x)
    simpa [S.spacing_eq] using this
  · obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
    simpa [S.spacing_eq] using h x


theorem svec_sym (φ : G.Ω 1 × Fin N → ℂ) (y : Torus d (N₀ * L ^ k)) (i : Fin N) :
    svec G' (S.fld φ) (σ y) i = svec G φ y i := by
  by_cases hy : y ∈ G.Ω 1
  · have h' : σ y ∈ G'.Ω 1 := (S.mem_Ω1 y).2 hy
    have := S.fld_apply φ ⟨y, hy⟩ i
    have e : (S.Ω1Equiv ⟨y, hy⟩ : G'.Ω 1) = ⟨σ y, h'⟩ := rfl
    rw [e] at this
    rw [svec_of_mem G' (S.fld φ) ⟨σ y, h'⟩ i]
    rw [show svec G φ y i = svec G φ (⟨y, hy⟩ : G.Ω 1) i from rfl, svec_of_mem]
    exact this
  · rw [svec_of_not_mem G φ hy, svec_of_not_mem G' _ (fun h => hy ((S.mem_Ω1 y).1 h))]

theorem blockAvg_sym (φ : G.Ω 1 × Fin N → ℂ) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (i : Fin N) :
    blockAvg G' (S.fld φ) (σ x) i = blockAvg G φ x i := by
  obtain ⟨h1, hk, hl⟩ := G.layerIndex_spec hx
  unfold blockAvg
  rw [S.layerIndex_eq]
  congr 1
  refine (Finset.sum_equiv σ (fun y => ?_) (fun y _ => ?_)).symm
  · rw [S.blk_iff h1 hk ⟨x, hl⟩ x (σ y)]; simp
  · exact (S.svec_sym φ y i).symm

theorem barField_sym (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) (w : Torus d (N₀ * L ^ k))
    (i : Fin N) : barField G' (S.sym D).Ψ (S.fld φ) (σ w) i = barField G D.Ψ φ w i := by
  by_cases hw : w ∈ G.Ω 1
  · have h' : σ w ∈ G'.Ω 1 := (S.mem_Ω1 w).2 hw
    have := S.fld_apply φ ⟨w, hw⟩ i
    have e : (S.Ω1Equiv ⟨w, hw⟩ : G'.Ω 1) = ⟨σ w, h'⟩ := rfl
    rw [e] at this
    simp only [barField, hw, h', ↓reduceDIte]
    exact this
  · have h' : σ w ∉ G'.Ω 1 := fun h => hw ((S.mem_Ω1 w).1 h)
    simp [barField, hw, h', sym]


theorem action_sym (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    action G' a ν (S.sym D) (S.fld φ) = action G a ν D φ := by
  unfold action
  have t1 : ∑ x : G'.Ω 1, (a (G'.layerIndex (x : Torus d (N₀ * L ^ k))) /
      ((L : ℝ) ^ G'.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) *
      ∑ i, ‖(S.sym D).Ψ x i - blockAvg G' (S.fld φ) x i‖ ^ 2 =
      ∑ x : G.Ω 1, (a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) *
      ∑ i, ‖D.Ψ x i - blockAvg G φ x i‖ ^ 2 := by
    rw [← Equiv.sum_comp S.Ω1Equiv]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [coe_Ω1Equiv, S.layerIndex_eq, sym, Equiv.symm_apply_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [S.blockAvg_sym φ x.2 i]
  have t3 : ∑ x : G'.Ω 1, ∑ i, ‖S.fld φ (x, i) - (S.sym D).h x i‖ ^ 2 =
      ∑ x : G.Ω 1, ∑ i, ‖φ (x, i) - D.h x i‖ ^ 2 := by
    rw [← Equiv.sum_comp S.Ω1Equiv]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp [sym]
  have t2 : ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d,
      (if x ∈ G'.Ω 1 ∨ x + Pi.single μ 1 ∈ G'.Ω 1 then
        ∑ i, ‖barField G' (S.sym D).Ψ (S.fld φ) (x + Pi.single μ 1) i -
          barField G' (S.sym D).Ψ (S.fld φ) x i‖ ^ 2 else 0) =
      ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, ‖barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i‖ ^ 2 else 0) := by
    rw [← Equiv.sum_comp σ, Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    rw [← Equiv.sum_comp S.perm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have hb := S.barField_sym D φ
    have hstep := S.step
    have hsub := S.step_sub
    cases hf : S.flip μ
    · refine Finset.sum_congr rfl fun x _ => ?_
      have e := hstep x μ
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at e
      rw [← e]
      simp only [S.omega 1 le_rfl (by omega), hb]
    · conv_rhs => rw [← Equiv.sum_comp (Equiv.subRight (Pi.single μ 1 : Torus d (N₀ * L ^ k)))]
      refine Finset.sum_congr rfl fun x _ => ?_
      have e := hsub x μ
      simp only [hf, ↓reduceIte] at e
      simp only [Equiv.subRight_apply, sub_add_cancel]
      rw [← e]
      simp only [S.omega 1 le_rfl (by omega), hb, norm_sub_rev (barField G D.Ψ φ (x - Pi.single μ 1) _)]
      simp only [or_comm]
  rw [t1, t2, t3]

/-- The multiplier transport as an equivalence. -/
def mulEquiv : (G.Ω 1 → ℂ) ≃ (G'.Ω 1 → ℂ) := Equiv.arrowCongr S.Ω1Equiv (Equiv.refl ℂ)

theorem isRealUnitField_sym_iff (φ : G.Ω 1 × Fin N → ℂ) :
    IsRealUnitField G' (S.fld φ) ↔ IsRealUnitField G φ := by
  unfold IsRealUnitField
  refine ⟨fun h x => ?_, fun h y => ?_⟩
  · simpa using h (S.Ω1Equiv x)
  · obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
    simpa using h x

theorem isReal_sym_iff (D : BgData G N) : (S.sym D).IsReal ↔ D.IsReal := by
  refine ⟨fun h x i => ?_, S.isReal_sym⟩
  simpa [sym] using h (σ x) i

theorem isMinimizer_sym_iff (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    IsMinimizer G' a ν (S.sym D) (S.fld φ) ↔ IsMinimizer G a ν D φ := by
  unfold IsMinimizer
  refine and_congr (S.isReal_sym_iff D) (and_congr (S.isRealUnitField_sym_iff φ) ?_)
  constructor
  · intro h σ₁ hσ₁
    have := h (S.fld σ₁) ((S.isRealUnitField_sym_iff σ₁).2 hσ₁)
    rwa [S.action_sym, S.action_sym] at this
  · intro h σ₂ hσ₂
    have e : σ₂ = S.fld (S.fldEquiv.symm σ₂) := (S.fldEquiv.apply_symm_apply σ₂).symm
    rw [e] at hσ₂ ⊢
    rw [S.action_sym, S.action_sym]
    exact h _ ((S.isRealUnitField_sym_iff _).1 hσ₂)

/-- **Lattice-symmetry covariance of the real background field.** -/
theorem bgField_sym (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) :
    bgField G' a ν (S.sym D) = S.fld (bgField G a ν D) := by
  classical
  have := dite_existsUnique_equiv S.fldEquiv (P := fun φ => IsMinimizer G a ν D φ)
    (Q := fun φ => IsMinimizer G' a ν (S.sym D) φ)
    (fun φ => (S.isMinimizer_sym_iff a ν D φ).symm) (fun φ => S.fld φ) (fun φ => φ)
    (fun φ => rfl) (S.fld 0)
  have h0 : S.fld (0 : G.Ω 1 × Fin N → ℂ) = 0 := by funext p; simp [fld]
  rw [h0] at this
  unfold bgField
  rw [← this]
  split_ifs <;> simp [h0]


/-- The real multiplier is transported by `σ`. -/
theorem bgMult_sym (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) :
    bgMult G' a ν (S.sym D) = S.mul (bgMult G a ν D) := by
  funext y
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
  rw [S.mul_apply]
  unfold bgMult
  rw [S.bgField_sym a ν D]
  have h0 : (0 : G'.Ω 1 → ℂ) = S.mul 0 := rfl
  rw [h0]
  simp only [Pi.sub_apply, S.fld_apply, S.liftOp_sym, S.source_sym]

theorem isSmallSolution_sym_iff' (a : ℕ → ℝ) (ν c₀ : ℝ) (D : BgData G N)
    (s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) :
    IsSmallSolution G a ν c₀ D s.1 s.2 ↔
      IsSmallSolution G' a ν c₀ (S.sym D) (S.fldEquiv.prodCongr S.mulEquiv s).1
        (S.fldEquiv.prodCongr S.mulEquiv s).2 :=
  (S.isSmallSolution_sym_iff a ν c₀ D s.1 s.2).symm

/-- **Lattice-symmetry covariance of the complex background field and multiplier.** -/
theorem bgFieldC_sym (a : ℕ → ℝ) (ν c₀ : ℝ) (D : BgData G N) :
    bgFieldC G' a ν c₀ (S.sym D) = S.fld (bgFieldC G a ν c₀ D) ∧
      bgMultC G' a ν c₀ (S.sym D) = S.mul (bgMultC G a ν c₀ D) := by
  classical
  have h0 : S.fld (0 : G.Ω 1 × Fin N → ℂ) = 0 := by funext p; simp [fld]
  have h0' : S.mul (0 : G.Ω 1 → ℂ) = 0 := rfl
  constructor
  · have := dite_existsUnique_equiv (S.fldEquiv.prodCongr S.mulEquiv)
      (P := fun s => IsSmallSolution G a ν c₀ D s.1 s.2)
      (Q := fun s => IsSmallSolution G' a ν c₀ (S.sym D) s.1 s.2)
      (S.isSmallSolution_sym_iff' a ν c₀ D) (fun s => S.fld s.1) (fun s => s.1)
      (fun s => rfl) (S.fld 0)
    rw [h0] at this
    unfold bgFieldC
    rw [← this]
    split_ifs <;> simp [h0]
  · have := dite_existsUnique_equiv (S.fldEquiv.prodCongr S.mulEquiv)
      (P := fun s => IsSmallSolution G a ν c₀ D s.1 s.2)
      (Q := fun s => IsSmallSolution G' a ν c₀ (S.sym D) s.1 s.2)
      (S.isSmallSolution_sym_iff' a ν c₀ D) (fun s => S.mul s.2) (fun s => s.2)
      (fun s => rfl) (S.mul 0)
    rw [h0'] at this
    unfold bgMultC
    rw [← this]
    split_ifs <;> simp [h0']


end LatSymm

section Generators

/-- The coordinate permutation `x ↦ x ∘ π⁻¹` of the torus. -/
def coordPerm (π : Equiv.Perm (Fin d)) : Equiv.Perm (Torus d (N₀ * L ^ k)) where
  toFun x := x ∘ π.symm
  invFun x := x ∘ π
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

omit [NeZero N₀] [NeZero L] in
theorem coordPerm_single (π : Equiv.Perm (Fin d)) (μ : Fin d) :
    coordPerm (N₀ := N₀) (L := L) (k := k) π (Pi.single μ 1) = Pi.single (π μ) 1 := by
  funext i
  simp only [coordPerm, Equiv.coe_fn_mk, Function.comp_apply, Pi.single_apply]
  simp [Equiv.symm_apply_eq]

/-- The coordinate permutations are symmetries of the paved torus (at every scale). -/
def TorusSymm.ofCoordPerm (j : ℕ) (π : Equiv.Perm (Fin d)) :
    TorusSymm (L := L) (N₀ := N₀) (k := k) j (coordPerm π) where
  perm := π
  flip := fun _ => false
  step := fun x μ => by
    simp only [Bool.false_eq_true, ↓reduceIte]
    have : coordPerm (N₀ := N₀) (L := L) (k := k) π (x + Pi.single μ 1) =
        coordPerm π x + coordPerm π (Pi.single μ 1) := by
      funext i; rfl
    rw [this, coordPerm_single]
  block := fun n h1 hnj hk x y => by
    have key : ∀ z : Torus d (N₀ * L ^ k), jBlock d L N₀ k n (coordPerm π z) =
        jBlock d L N₀ k n z ∘ π.symm := fun z => rfl
    rw [key, key]
    constructor
    · intro h
      funext i
      simpa using congrFun h (π i)
    · intro h
      rw [h]

omit [NeZero N₀] [NeZero L] in
theorem jBlock_apply (n : ℕ) (x : Torus d (N₀ * L ^ k)) (i : Fin d) :
    jBlock d L N₀ k n x i = blockCoord (L ^ n) (N₀ * L ^ (k - n)) (x i) := rfl

/-- Translation by a multiple of `L ^ j` is a symmetry of the paved torus up to scale `j`. -/
def TorusSymm.ofTranslate (j : ℕ) (t : Torus d (N₀ * L ^ k)) (ht : ∀ μ, L ^ j ∣ (t μ).val) :
    TorusSymm j (Equiv.addRight t : Equiv.Perm (Torus d (N₀ * L ^ k))) where
  perm := 1
  flip := fun _ => false
  step := fun x μ => by
    simp only [Equiv.coe_addRight, Bool.false_eq_true, ↓reduceIte, Equiv.Perm.coe_one, id_eq]
    abel
  block := fun n h1 hnj hk x y => by
    have hdvd : ∀ μ, L ^ n ∣ (t μ).val := fun μ => (pow_dvd_pow L hnj).trans (ht μ)
    have hℓ : N₀ * L ^ k = L ^ n * (N₀ * L ^ (k - n)) := side_eq hk
    have key : ∀ z : Torus d (N₀ * L ^ k), jBlock d L N₀ k n (z + t) =
        fun i => jBlock d L N₀ k n z i + (((t i).val / L ^ n : ℕ) : ZMod (N₀ * L ^ (k - n))) :=
      fun z => funext fun i => by
        rw [jBlock_apply, Pi.add_apply, blockCoord_add_of_dvd hℓ _ _ (hdvd i)]; rfl
    simp only [Equiv.coe_addRight, key]
    constructor
    · intro h; funext i; simpa using congrFun h i
    · intro h; funext i; simp [congrFun h i]

/-- The reflection `x_μ ↦ c - 1 - x_μ` of the coordinate `μ` of the torus. -/
def reflPerm (μ₀ : Fin d) (c : ZMod (N₀ * L ^ k)) : Equiv.Perm (Torus d (N₀ * L ^ k)) where
  toFun x := Function.update x μ₀ (c - 1 - x μ₀)
  invFun x := Function.update x μ₀ (c - 1 - x μ₀)
  left_inv x := by funext i; by_cases h : i = μ₀ <;> simp [h]
  right_inv x := by funext i; by_cases h : i = μ₀ <;> simp [h]

/-- The reflection `x_μ ↦ c - 1 - x_μ`, `L ^ j ∣ c`, maps `L ^ n`-blocks to `L ^ n`-blocks for
`n ≤ j`: it is a symmetry of the paved torus up to scale `j`. -/
def TorusSymm.ofReflect (j : ℕ) (μ₀ : Fin d) (c : ZMod (N₀ * L ^ k)) (hcd : L ^ j ∣ c.val) :
    TorusSymm j (reflPerm μ₀ c) where
  perm := 1
  flip := fun μ => decide (μ = μ₀)
  step := fun x μ => by
    funext i
    by_cases hi : i = μ₀ <;> by_cases hm : μ = μ₀ <;> simp [reflPerm, hi, hm, Pi.single_apply]
    all_goals ring
  block := fun n h1 hnj hk x y => by
    have hℓ : N₀ * L ^ k = L ^ n * (N₀ * L ^ (k - n)) := side_eq hk
    have hc : 0 < L ^ n := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
    have hdvd : L ^ n ∣ c.val := (pow_dvd_pow L hnj).trans hcd
    have key : ∀ (z : Torus d (N₀ * L ^ k)) i, jBlock d L N₀ k n (reflPerm μ₀ c z) i =
        if i = μ₀ then -1 - jBlock d L N₀ k n z i +
          ((c.val / L ^ n : ℕ) : ZMod (N₀ * L ^ (k - n))) else jBlock d L N₀ k n z i := by
      intro z i
      by_cases hi : i = μ₀
      · subst hi
        simp only [jBlock_apply, reflPerm, Equiv.coe_fn_mk, Function.update_self, ite_true]
        have e : c - 1 - z i = (-1 - z i) + c := by ring
        rw [e, blockCoord_add_of_dvd hℓ _ _ hdvd, blockCoord_neg_one_sub hc hℓ _]
      · simp [jBlock_apply, reflPerm, hi]
    constructor
    · intro h; funext i
      have := congrFun h i
      rw [key, key] at this
      by_cases hi : i = μ₀
      · subst hi; simpa using this
      · simpa [hi] using this
    · intro h; funext i
      rw [key, key]
      by_cases hi : i = μ₀
      · subst hi; simp [congrFun h i]
      · simp [hi, congrFun h i]

end Generators

section Compose

/-- The identity has the lattice structure of a symmetry. -/
def NbrSymm.refl : NbrSymm (1 : Equiv.Perm (Torus d (N₀ * L ^ k))) where
  perm := 1
  flip := fun _ => false
  step := fun x μ => by simp

/-- Composition of lattice structures (first `σ`, then `τ`). -/
def NbrSymm.trans {σ τ : Equiv.Perm (Torus d (N₀ * L ^ k))} (S : NbrSymm σ) (S' : NbrSymm τ) :
    NbrSymm (σ.trans τ) where
  perm := S.perm.trans S'.perm
  flip := fun μ => xor (S.flip μ) (S'.flip (S.perm μ))
  step := fun x μ => by
    have h1 := S.step x μ
    have h2 := S'.step (σ x) (S.perm μ)
    have h3 := S'.step_sub (σ x) (S.perm μ)
    simp only [Equiv.trans_apply, h1]
    cases hf : S.flip μ <;> cases hf' : S'.flip (S.perm μ) <;>
      simp [hf', h2, h3] at h2 h3 ⊢

/-- The inverse of a lattice structure. -/
def NbrSymm.symm {σ : Equiv.Perm (Torus d (N₀ * L ^ k))} (S : NbrSymm σ) : NbrSymm σ.symm where
  perm := S.perm.symm
  flip := fun μ => S.flip (S.perm.symm μ)
  step := fun y μ => by
    have h1 := S.step (σ.symm y) (S.perm.symm μ)
    have h2 := S.step_sub (σ.symm y) (S.perm.symm μ)
    simp only [Equiv.apply_symm_apply] at h1 h2
    cases hf : S.flip (S.perm.symm μ)
    · simp only [hf, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
      exact σ.symm_apply_eq.2 (by rw [h1])
    · simp only [hf, ↓reduceIte] at h1 h2 ⊢
      exact σ.symm_apply_eq.2 (by rw [h2])

/-- The identity is a symmetry of the paved torus. -/
def TorusSymm.refl (j : ℕ) : TorusSymm j (1 : Equiv.Perm (Torus d (N₀ * L ^ k))) :=
  { NbrSymm.refl with block := fun _ _ _ _ _ _ => Iff.rfl }

/-- Composition of symmetries of the paved torus (first `σ`, then `τ`). -/
def TorusSymm.trans {j : ℕ} {σ τ : Equiv.Perm (Torus d (N₀ * L ^ k))} (S : TorusSymm j σ)
    (S' : TorusSymm j τ) : TorusSymm j (σ.trans τ) :=
  { S.toNbrSymm.trans S'.toNbrSymm with
    block := fun n h1 hnj hk x y => by
      simp only [Equiv.trans_apply]
      rw [S'.block n h1 hnj hk, S.block n h1 hnj hk] }

/-- The inverse of a symmetry of the paved torus. -/
def TorusSymm.symm {j : ℕ} {σ : Equiv.Perm (Torus d (N₀ * L ^ k))} (S : TorusSymm j σ) :
    TorusSymm j σ.symm :=
  { S.toNbrSymm.symm with
    block := fun n h1 hnj hk x y => by
      simpa using (S.block n h1 hnj hk (σ.symm x) (σ.symm y)).symm }

end Compose

section LatSymmGens

variable {G G' G'' : GeneratingSet d L N₀ k ϱ}

/-- A symmetry of the paved torus up to scale `j` that maps `Ω_i` onto `Ω'_i` is a lattice symmetry
as soon as all layers of `G` have scale `≤ j`. -/
def LatSymm.ofTorusSymm {j : ℕ} {σ : Equiv.Perm (Torus d (N₀ * L ^ k))} (T : TorusSymm j σ)
    (hΩ : ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ x, σ x ∈ G'.Ω i ↔ x ∈ G.Ω i)
    (hj : ∀ n, 1 ≤ n → n ≤ k → (G.layer n).Nonempty → n ≤ j) : LatSymm G G' σ :=
  { T.toNbrSymm with
    omega := hΩ
    block := fun n h1 hk hne x y => T.block n h1 (hj n h1 hk hne) hk x y }

/-- The identity is a lattice symmetry. -/
def LatSymm.refl (G : GeneratingSet d L N₀ k ϱ) :
    LatSymm G G (1 : Equiv.Perm (Torus d (N₀ * L ^ k))) :=
  { NbrSymm.refl with
    omega := fun _ _ _ _ => Iff.rfl
    block := fun _ _ _ _ _ _ => Iff.rfl }

/-- Composition of lattice symmetries (first `σ`, then `τ`). -/
def LatSymm.trans {σ τ : Equiv.Perm (Torus d (N₀ * L ^ k))}
    (S : LatSymm G G' σ) (S' : LatSymm G' G'' τ) : LatSymm G G'' (σ.trans τ) :=
  { S.toNbrSymm.trans S'.toNbrSymm with
    omega := fun j h1 h2 x => by
      simp only [Equiv.trans_apply]
      rw [S'.omega j h1 h2, S.omega j h1 h2]
    block := fun n h1 hk hne x y => by
      obtain ⟨z, hz⟩ := hne
      simp only [Equiv.trans_apply]
      rw [S'.block n h1 hk ⟨σ z, (S.mem_layer h1 hk z).2 hz⟩, S.block n h1 hk ⟨z, hz⟩] }

/-- The inverse of a lattice symmetry is a lattice symmetry in the opposite direction. -/
def LatSymm.symm {σ : Equiv.Perm (Torus d (N₀ * L ^ k))} (S : LatSymm G G' σ) :
    LatSymm G' G σ.symm :=
  { S.toNbrSymm.symm with
    omega := fun j h1 h2 y => by
      simpa using (S.omega j h1 h2 (σ.symm y)).symm
    block := fun n h1 hk hne x y => by
      obtain ⟨z, hz⟩ := hne
      have hz' : σ.symm z ∈ G.layer n := by
        have := (S.mem_layer h1 hk (σ.symm z)).1
        exact this (by simpa using hz)
      simpa using (S.block n h1 hk ⟨σ.symm z, hz'⟩ (σ.symm x) (σ.symm y)).symm }

/-- The coordinate permutation is a lattice symmetry as soon as it preserves the generating
set. -/
def LatSymm.ofCoordPerm (π : Equiv.Perm (Fin d))
    (hΩ : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ x, coordPerm π x ∈ G'.Ω j ↔ x ∈ G.Ω j) :
    LatSymm G G' (coordPerm π) :=
  LatSymm.ofTorusSymm (TorusSymm.ofCoordPerm k π) hΩ (fun _ _ hk _ => hk)

/-- Translation by a multiple of `L ^ j` is a lattice symmetry as soon as it preserves the
generating set and all layers of `G` have scale `≤ j`. -/
def LatSymm.ofTranslate (j : ℕ) (t : Torus d (N₀ * L ^ k)) (ht : ∀ μ, L ^ j ∣ (t μ).val)
    (hΩ : ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ x, x + t ∈ G'.Ω i ↔ x ∈ G.Ω i)
    (hj : ∀ n, 1 ≤ n → n ≤ k → (G.layer n).Nonempty → n ≤ j) :
    LatSymm G G' (Equiv.addRight t) :=
  LatSymm.ofTorusSymm (TorusSymm.ofTranslate j t ht) hΩ hj

/-- The reflection `x_μ ↦ c - 1 - x_μ`, `L ^ j ∣ c`, is a lattice symmetry as soon as it preserves
the generating set and all layers of `G` have scale `≤ j`. -/
def LatSymm.ofReflect (j : ℕ) (μ₀ : Fin d) (c : ZMod (N₀ * L ^ k)) (hcd : L ^ j ∣ c.val)
    (hΩ : ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ x, reflPerm μ₀ c x ∈ G'.Ω i ↔ x ∈ G.Ω i)
    (hj : ∀ n, 1 ≤ n → n ≤ k → (G.layer n).Nonempty → n ≤ j) :
    LatSymm G G' (reflPerm μ₀ c) :=
  LatSymm.ofTorusSymm (TorusSymm.ofReflect j μ₀ c hcd) hΩ hj

end LatSymmGens

end Balaban.Background
