/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.GenSetStabilityCore
public import Balaban.LargeField.R.WindowConvPhysReadTransport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Transport of the Euler–Lagrange system between two generating sets on a ball

Two generating sets `Gl`, `Gw` on tori identified by a bijection `e : 𝕋_w ≃ 𝕋_l` commuting with the
lattice steps and carrying `n`-blocks to `n`-blocks (`n ≤ k_l`).  On a set `A` of sites the layers
agree: `x ∈ Ω^l_n ↔ e⁻¹ x ∈ Ω^w_n` for `1 ≤ n ≤ k_l + 1`.  For the solution `(φ_w, α_w)` of (EL) on
`Gw` with datum `D_w`:

* `exists_transportData`: a datum `D'` of `Gl` with `h̃' = h̃_l` that equals `D_w ∘ e⁻¹` at the data
  sites of `Gl` whose block lies in `A` (and `D_l` at the others);
* `elResidual_transport`: at a site `x ∈ Ω^l_1` whose block and neighbours (with their blocks) lie in
  `A`, the residual of the linear equation of (EL) of `Gl` for `D'` at the transported field
  `transportField e Ψ_w φ_w` and multiplier `α_w ∘ e⁻¹` is the residual of `Gw` at `e⁻¹ x`;
* `isEL_restrict_transport`: for `G_B ≺ Gl` with `Ω^B_1` inside that region, the restriction of the
  transported pair solves (EL) of `G_B` for the composed datum (P2 §4, Theorem 6.1 (ii)).
-/

@[expose] public section

namespace Balaban.Background

open Balaban Balaban.Multiscale Balaban.LargeField.ActionConv Finset

section Transport

variable {d L N N₀l kl N₀w kw : ℕ} [NeZero N₀l] [NeZero N₀w] [NeZero L] {ϱl ϱw : ℝ}
  {Gl : GeneratingSet d L N₀l kl ϱl} {Gw : GeneratingSet d L N₀w kw ϱw}
  {e : Torus d (N₀w * L ^ kw) ≃ Torus d (N₀l * L ^ kl)}
  {A : Set (Torus d (N₀l * L ^ kl))}

/-- On the set where the layers agree, the layer indices agree. -/
theorem layerIndex_transport (hk : kl ≤ kw)
    (hag : ∀ x ∈ A, ∀ n, 1 ≤ n → n ≤ kl + 1 → (x ∈ Gl.Ω n ↔ e.symm x ∈ Gw.Ω n))
    {x : Torus d (N₀l * L ^ kl)} (hx : x ∈ A) : Gw.layerIndex (e.symm x) = Gl.layerIndex x := by
  by_cases hx1 : x ∈ Gl.Ω 1
  · obtain ⟨hn1, hnk, hxn⟩ := Gl.layerIndex_spec hx1
    have hxl := Gl.mem_layer.1 hxn
    have h1 : e.symm x ∈ Gw.Ω (Gl.layerIndex x) := (hag x hx _ hn1 (by omega)).1 hxl.1
    have h2 : e.symm x ∉ Gw.Ω (Gl.layerIndex x + 1) := fun h =>
      hxl.2 ((hag x hx _ (by omega) (by omega)).2 h)
    exact Gw.layerIndex_eq hn1 (hnk.trans hk) (Gw.mem_layer.2 ⟨h1, h2⟩)
  · have h1 : e.symm x ∉ Gw.Ω 1 := fun h => hx1 ((hag x hx 1 le_rfl (by omega)).2 h)
    rw [layerIndex_of_not_mem Gw h1, layerIndex_of_not_mem Gl hx1]

/-- Blocks correspond. -/
theorem blk_transport
    (hblk : ∀ n, n ≤ kl → ∀ x y, jBlock d L N₀l kl n x = jBlock d L N₀l kl n y ↔
      jBlock d L N₀w kw n (e.symm x) = jBlock d L N₀w kw n (e.symm y))
    {n : ℕ} (hn : n ≤ kl) (x y : Torus d (N₀l * L ^ kl)) :
    y ∈ Gl.blk n x ↔ e.symm y ∈ Gw.blk n (e.symm x) := by
  rw [GeneratingSet.mem_blk, GeneratingSet.mem_blk]
  exact hblk n hn y x

open Classical in
/-- **The transported datum.**  There is a datum `D'` of `Gl` with `h̃' = h̃_l` whose field is
`Ψ_w ∘ e⁻¹` at the data sites whose block (of their `Gl`-layer) lies in `A`, and `Ψ_l` at the
other data sites. -/
theorem exists_transportData (hk : kl ≤ kw)
    (hag : ∀ x ∈ A, ∀ n, 1 ≤ n → n ≤ kl + 1 → (x ∈ Gl.Ω n ↔ e.symm x ∈ Gw.Ω n))
    (hblk : ∀ n, n ≤ kl → ∀ x y, jBlock d L N₀l kl n x = jBlock d L N₀l kl n y ↔
      jBlock d L N₀w kw n (e.symm x) = jBlock d L N₀w kw n (e.symm y))
    (Dl : BgData Gl N) (Dw : BgData Gw N) :
    ∃ D' : BgData Gl N, (∀ x, D'.h x = Dl.h x) ∧
      ∀ x ∈ dataSites Gl, ((∀ y ∈ Gl.blk (Gl.layerIndex x) x, y ∈ A) →
        D'.Ψ x = Dw.Ψ (e.symm x)) ∧
        (¬ (∀ y ∈ Gl.blk (Gl.layerIndex x) x, y ∈ A) → D'.Ψ x = Dl.Ψ x) := by
  set P : Torus d (N₀l * L ^ kl) → Prop := fun x => ∀ y ∈ Gl.blk (Gl.layerIndex x) x, y ∈ A
    with hP
  set Ψ'' : Torus d (N₀l * L ^ kl) → Fin N → ℂ :=
    fun x => if P x then Dw.Ψ (e.symm x) else Dl.Ψ x with hΨ''
  have hlc : IsLayerConstant Gl Ψ'' := by
    intro n hn1 hnk x hx x' hx'
    have hb := GeneratingSet.mem_blk.1 hx'
    have hx'l : x' ∈ Gl.layer n := (Gl.mem_layer_iff hn1 hnk hb).2 hx
    have hlx : Gl.layerIndex x = n := Gl.layerIndex_eq hn1 hnk hx
    have hlx' : Gl.layerIndex x' = n := Gl.layerIndex_eq hn1 hnk hx'l
    have hbb : Gl.blk n x' = Gl.blk n x := by
      ext y; simp only [GeneratingSet.mem_blk, hb]
    have hPP : P x' ↔ P x := by
      simp only [hP, hlx, hlx', hbb]
    by_cases hPx : P x
    · have hPx' : P x' := hPP.2 hPx
      simp only [hΨ'', hPx, hPx', ↓reduceIte]
      have hxA : x ∈ A := hPx x (by rw [hlx]; exact GeneratingSet.mem_blk.2 rfl)
      have hlay := layerIndex_transport hk hag hxA
      have hxw : e.symm x ∈ Gw.layer n := by
        have hx1 := Gl.layer_subset hn1 hnk hx
        have hxw1 : e.symm x ∈ Gw.Ω 1 := (hag x hxA 1 le_rfl (by omega)).1 hx1
        obtain ⟨-, -, h⟩ := Gw.layerIndex_spec hxw1
        rwa [hlay, hlx] at h
      have hx'w : e.symm x' ∈ Gw.blk n (e.symm x) := (blk_transport hblk hnk x x').1 hx'
      exact Dw.Ψ_layerConst n hn1 (hnk.trans hk) (e.symm x) hxw (e.symm x') hx'w
    · have hPx' : ¬ P x' := fun h => hPx (hPP.1 h)
      simp only [hΨ'', hPx, hPx', ↓reduceIte]
      exact Dl.Ψ_layerConst n hn1 hnk x hx x' hx'
  refine ⟨BgData.clip Gl Ψ'' Dl.h hlc Dl.h_layerConst, fun x => ?_, fun x hx => ⟨fun h => ?_,
    fun h => ?_⟩⟩
  · simp only [BgData.clip]
    split_ifs with h
    · rfl
    · exact (Dl.h_zero x h).symm
  · simp only [BgData.clip, hx, ↓reduceIte, hΨ'']
    split_ifs with h'
    · rfl
    · exact absurd h h'
  · simp only [BgData.clip, hx, ↓reduceIte, hΨ'']
    split_ifs with h'
    · exact absurd h' h
    · rfl

/-- At a site of `Ω^l_1`, the extension of the transported field is the extension of `φ_w` at
`e⁻¹ x`. -/
theorem barField_transport_of_mem (D' : BgData Gl N) (Dw : BgData Gw N)
    (φw : Gw.Ω 1 × Fin N → ℂ) {x : Torus d (N₀l * L ^ kl)} (hx : x ∈ Gl.Ω 1) (i : Fin N) :
    barField Gl D'.Ψ (transportField (Gl := Gl) e Dw.Ψ φw) x i = barField Gw Dw.Ψ φw (e.symm x) i := by
  classical
  simp [barField, hx, transportField]

/-- Off `Ω^l_1`, the extension of the transported field is `Ψ_w ∘ e⁻¹` when the data agree there. -/
theorem barField_transport_of_not_mem
    (hag : ∀ x ∈ A, ∀ n, 1 ≤ n → n ≤ kl + 1 → (x ∈ Gl.Ω n ↔ e.symm x ∈ Gw.Ω n))
    (D' : BgData Gl N) (Dw : BgData Gw N) (φw : Gw.Ω 1 × Fin N → ℂ)
    {x : Torus d (N₀l * L ^ kl)} (hxA : x ∈ A) (hx : x ∉ Gl.Ω 1)
    (hΨ : D'.Ψ x = Dw.Ψ (e.symm x)) (i : Fin N) :
    barField Gl D'.Ψ (transportField (Gl := Gl) e Dw.Ψ φw) x i = barField Gw Dw.Ψ φw (e.symm x) i := by
  classical
  have hxw : e.symm x ∉ Gw.Ω 1 := fun h => hx ((hag x hxA 1 le_rfl (by omega)).2 h)
  simp [barField, hx, hxw, hΨ]

end Transport

section Residual

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {a : ℕ → ℝ} {ν : ℝ}

/-- The residual of the linear equation of (EL) through the residual `S - H_D(0) φ̄`. -/
theorem elResidual_eq_sub_residual (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ)
    (p : G.Ω 1 × Fin N) :
    elResidual G a ν D φ α p = α p.1 * φ p - residual G a ν D (barField G D.Ψ φ) p := by
  classical
  have e : (fun q : G.Ω 1 × Fin N => barField G D.Ψ φ q.1 q.2) = φ := by
    funext q; simp [barField, q.1.2]
  unfold elResidual residual
  rw [e]
  simp only [Pi.sub_apply]
  rw [H_alpha_apply]
  ring

/-- The collar terms of the residual vanish at the extension `φ̄` by the data. -/
theorem collar_term_barField (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) (z : Torus d (N₀ * L ^ k))
    (i : Fin N) :
    (if z ∈ collar G then D.Ψ z i - barField G D.Ψ φ z i else 0) = 0 := by
  classical
  split_ifs with h
  · have hz : z ∉ G.Ω 1 := ((mem_collar G).1 h).1
    simp [barField, hz]
  · rfl

end Residual

section TransportEL

variable {d L N N₀l kl N₀w kw : ℕ} [NeZero N₀l] [NeZero N₀w] [NeZero L] {ϱl ϱw : ℝ}
  {Gl : GeneratingSet d L N₀l kl ϱl} {Gw : GeneratingSet d L N₀w kw ϱw}
  {e : Torus d (N₀w * L ^ kw) ≃ Torus d (N₀l * L ^ kl)}
  {A : Set (Torus d (N₀l * L ^ kl))}

omit [NeZero N₀l] [NeZero N₀w] [NeZero L] in
theorem symm_add_single (he : ∀ x μ, e (x + Pi.single μ 1) = e x + Pi.single μ 1)
    (y : Torus d (N₀l * L ^ kl)) (μ : Fin d) :
    e.symm (y + Pi.single μ 1) = e.symm y + Pi.single μ 1 := by
  apply e.injective
  rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

omit [NeZero N₀l] [NeZero N₀w] [NeZero L] in
theorem symm_sub_single (he : ∀ x μ, e (x + Pi.single μ 1) = e x + Pi.single μ 1)
    (y : Torus d (N₀l * L ^ kl)) (μ : Fin d) :
    e.symm (y - Pi.single μ 1) = e.symm y - Pi.single μ 1 := by
  have h := symm_add_single he (y - Pi.single μ 1) μ
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

open Classical in
/-- **Transport of the residual of (EL).**  At a site `x ∈ Ω^l_1` such that `x`, its neighbours and
the blocks of all of them lie in `A` (where the layers agree), with the transported datum `D'`
equal to `D_w ∘ e⁻¹` at the data sites read there and `h̃_l(x) = h̃_w(e⁻¹ x)`, the residual of the
linear equation of (EL) of `Gl` at the transported pair equals that of `Gw` at `e⁻¹ x`. -/
theorem elResidual_transport (hk : kl ≤ kw)
    (he : ∀ x μ, e (x + Pi.single μ 1) = e x + Pi.single μ 1)
    (hag : ∀ x ∈ A, ∀ n, 1 ≤ n → n ≤ kl + 1 → (x ∈ Gl.Ω n ↔ e.symm x ∈ Gw.Ω n))
    (hblk : ∀ n, n ≤ kl → ∀ x y, jBlock d L N₀l kl n x = jBlock d L N₀l kl n y ↔
      jBlock d L N₀w kw n (e.symm x) = jBlock d L N₀w kw n (e.symm y))
    (a : ℕ → ℝ) (ν : ℝ) (D' : BgData Gl N) (Dw : BgData Gw N) (φw : Gw.Ω 1 × Fin N → ℂ)
    (αw : Gw.Ω 1 → ℂ) (x : Gl.Ω 1) (hx' : e.symm (x : Torus d (N₀l * L ^ kl)) ∈ Gw.Ω 1)
    (hxA : (x : Torus d (N₀l * L ^ kl)) ∈ A)
    (hΨx : D'.Ψ x = Dw.Ψ (e.symm x)) (hhx : D'.h x = Dw.h (e.symm x))
    (hnb : ∀ μ : Fin d,
      ((x : Torus d (N₀l * L ^ kl)) + Pi.single μ 1 ∈ A ∧
        ((x : Torus d (N₀l * L ^ kl)) + Pi.single μ 1 ∉ Gl.Ω 1 →
          D'.Ψ ((x : Torus d (N₀l * L ^ kl)) + Pi.single μ 1) =
            Dw.Ψ (e.symm ((x : Torus d (N₀l * L ^ kl)) + Pi.single μ 1)))) ∧
      ((x : Torus d (N₀l * L ^ kl)) - Pi.single μ 1 ∈ A ∧
        ((x : Torus d (N₀l * L ^ kl)) - Pi.single μ 1 ∉ Gl.Ω 1 →
          D'.Ψ ((x : Torus d (N₀l * L ^ kl)) - Pi.single μ 1) =
            Dw.Ψ (e.symm ((x : Torus d (N₀l * L ^ kl)) - Pi.single μ 1)))))
    (i : Fin N) :
    elResidual Gl a ν D' (transportField (Gl := Gl) e Dw.Ψ φw)
        (fun z => if h : e.symm (z : Torus d (N₀l * L ^ kl)) ∈ Gw.Ω 1 then αw ⟨_, h⟩ else 0)
        (x, i) =
      elResidual Gw a ν Dw φw αw (⟨e.symm x, hx'⟩, i) := by
  have hlay := layerIndex_transport hk hag hxA
  have hn1 := (Gl.layerIndex_spec x.2).1
  have hnk := (Gl.layerIndex_spec x.2).2.1
  set xw : Gw.Ω 1 := ⟨e.symm x, hx'⟩ with hxw
  -- the transported extension at sites of the block and at the neighbours
  have hbar_mem : ∀ y ∈ Gl.Ω 1, barField Gl D'.Ψ (transportField (Gl := Gl) e Dw.Ψ φw) y i =
      barField Gw Dw.Ψ φw (e.symm y) i := fun y hy => barField_transport_of_mem D' Dw φw hy i
  have hbar_nb : ∀ (y : Torus d (N₀l * L ^ kl)), y ∈ A →
      (y ∉ Gl.Ω 1 → D'.Ψ y = Dw.Ψ (e.symm y)) →
      barField Gl D'.Ψ (transportField (Gl := Gl) e Dw.Ψ φw) y i =
        barField Gw Dw.Ψ φw (e.symm y) i := by
    intro y hyA hyΨ
    by_cases hy : y ∈ Gl.Ω 1
    · exact hbar_mem y hy
    · exact barField_transport_of_not_mem hag D' Dw φw hyA hy (hyΨ hy) i
  have hplus : ∀ μ : Fin d, barField Gl D'.Ψ (transportField (Gl := Gl) e Dw.Ψ φw)
      ((x : Torus d (N₀l * L ^ kl)) + Pi.single μ 1) i =
      barField Gw Dw.Ψ φw ((xw : Torus d (N₀w * L ^ kw)) + Pi.single μ 1) i := by
    intro μ
    rw [hbar_nb _ (hnb μ).1.1 (hnb μ).1.2, symm_add_single he]
  have hminus : ∀ μ : Fin d, barField Gl D'.Ψ (transportField (Gl := Gl) e Dw.Ψ φw)
      ((x : Torus d (N₀l * L ^ kl)) - Pi.single μ 1) i =
      barField Gw Dw.Ψ φw ((xw : Torus d (N₀w * L ^ kw)) - Pi.single μ 1) i := by
    intro μ
    rw [hbar_nb _ (hnb μ).2.1 (hnb μ).2.2, symm_sub_single he]
  have hself : barField Gl D'.Ψ (transportField (Gl := Gl) e Dw.Ψ φw) x i =
      barField Gw Dw.Ψ φw xw i := hbar_mem x x.2
  have hsum : ∑ y ∈ Gl.blk (Gl.layerIndex (x : Torus d (N₀l * L ^ kl))) x,
      barField Gl D'.Ψ (transportField (Gl := Gl) e Dw.Ψ φw) y i =
      ∑ y ∈ Gw.blk (Gw.layerIndex (xw : Torus d (N₀w * L ^ kw))) xw, barField Gw Dw.Ψ φw y i := by
    rw [show (xw : Torus d (N₀w * L ^ kw)) = e.symm x from rfl, hlay]
    refine Finset.sum_nbij' (fun y => e.symm y) (fun y => e y) (fun y hy => ?_) (fun y hy => ?_)
      (fun y _ => e.apply_symm_apply y) (fun y _ => e.symm_apply_apply y) (fun y hy => ?_)
    · exact (blk_transport hblk hnk x y).1 hy
    · have := (blk_transport (Gl := Gl) (Gw := Gw) hblk hnk x (e y)).2
      rw [e.symm_apply_apply] at this
      exact this hy
    · have hyl : y ∈ Gl.layer (Gl.layerIndex x) := (Gl.mem_layer_iff hn1 hnk
        (GeneratingSet.mem_blk.1 hy)).2 (Gl.layerIndex_spec x.2).2.2
      exact hbar_mem y (Gl.layer_subset hn1 hnk hyl)
  rw [elResidual_eq_sub_residual, elResidual_eq_sub_residual, residual_apply, residual_apply]
  simp only [collar_term_barField, add_zero, Finset.sum_const_zero]
  rw [hsum, hself]
  simp only [hplus, hminus]
  have hα : (if h : e.symm (x : Torus d (N₀l * L ^ kl)) ∈ Gw.Ω 1 then αw ⟨_, h⟩ else 0) = αw xw := by
    simp only [hx', ↓reduceDIte]
    rfl
  have hφ : transportField (Gl := Gl) e Dw.Ψ φw (x, i) = φw (xw, i) := by
    classical
    simp [transportField, barField, hx', hxw]
  simp only [hα, hφ, hΨx, hhx, ← hlay]
  rfl

open Classical in
/-- **The transported pair restricted to `G_B ≺ Gl` solves (EL) of `G_B`** for the composed datum
(P2 §4, Theorem 6.1 (ii)), when every site of `Ω^B_1` satisfies the hypotheses of
`elResidual_transport`. -/
theorem isEL_restrict_transport (hk : kl ≤ kw)
    (he : ∀ x μ, e (x + Pi.single μ 1) = e x + Pi.single μ 1)
    (hag : ∀ x ∈ A, ∀ n, 1 ≤ n → n ≤ kl + 1 → (x ∈ Gl.Ω n ↔ e.symm x ∈ Gw.Ω n))
    (hblk : ∀ n, n ≤ kl → ∀ x y, jBlock d L N₀l kl n x = jBlock d L N₀l kl n y ↔
      jBlock d L N₀w kw n (e.symm x) = jBlock d L N₀w kw n (e.symm y))
    {ϱB : ℝ} {GB : GeneratingSet d L N₀l kl ϱB} (hp : Precedes GB Gl) (a : ℕ → ℝ)
    (ha : ∀ j, 1 ≤ j → j ≤ kl → a j ≠ 0) (ν : ℝ) (D' : BgData Gl N) (Dw : BgData Gw N)
    {φw : Gw.Ω 1 × Fin N → ℂ} {αw : Gw.Ω 1 → ℂ} (hEL : IsEL Gw a ν Dw φw αw)
    (hΩ : ∀ x ∈ GB.Ω 1, e.symm x ∈ Gw.Ω 1) (hA : ∀ x ∈ GB.Ω 1, x ∈ A)
    (hΨ : ∀ x ∈ GB.Ω 1, D'.Ψ x = Dw.Ψ (e.symm x))
    (hh : ∀ x ∈ GB.Ω 1, D'.h x = Dw.h (e.symm x))
    (hnb : ∀ x ∈ GB.Ω 1, ∀ μ : Fin d,
      (x + Pi.single μ 1 ∈ A ∧ (x + Pi.single μ 1 ∉ Gl.Ω 1 →
        D'.Ψ (x + Pi.single μ 1) = Dw.Ψ (e.symm (x + Pi.single μ 1)))) ∧
      (x - Pi.single μ 1 ∈ A ∧ (x - Pi.single μ 1 ∉ Gl.Ω 1 →
        D'.Ψ (x - Pi.single μ 1) = Dw.Ψ (e.symm (x - Pi.single μ 1))))) :
    IsEL GB a ν (composeData hp a (transportField (Gl := Gl) e Dw.Ψ φw) D')
      (hp.restrictφ (transportField (Gl := Gl) e Dw.Ψ φw))
      (hp.restrictα
        (fun z => if h : e.symm (z : Torus d (N₀l * L ^ kl)) ∈ Gw.Ω 1 then αw ⟨_, h⟩ else 0)) := by
  refine ⟨?_, fun x => ?_⟩
  · funext p
    obtain ⟨x, i⟩ := p
    have hx := x.2
    have e1 := elResidual_compose hp a ha ν D' (transportField (Gl := Gl) e Dw.Ψ φw)
      (fun z => if h : e.symm (z : Torus d (N₀l * L ^ kl)) ∈ Gw.Ω 1 then αw ⟨_, h⟩ else 0) x i
    have e2 := elResidual_transport hk he hag hblk a ν D' Dw φw αw (hp.incl x) (hΩ x hx)
      (hA x hx) (hΨ x hx) (hh x hx) (hnb x hx) i
    have e0 : elResidual Gw a ν Dw φw αw = 0 := by
      unfold elResidual; rw [hEL.1]; simp
    have h0 : elResidual GB a ν (composeData hp a (transportField (Gl := Gl) e Dw.Ψ φw) D')
        (hp.restrictφ (transportField (Gl := Gl) e Dw.Ψ φw))
        (hp.restrictα
          (fun z => if h : e.symm (z : Torus d (N₀l * L ^ kl)) ∈ Gw.Ω 1 then αw ⟨_, h⟩ else 0))
        (x, i) = 0 := by
      rw [e1, e2, e0]; rfl
    unfold elResidual at h0
    exact sub_eq_zero.1 h0
  · have hx := x.2
    have hxw := hΩ x hx
    have e3 : ∀ i, hp.restrictφ (transportField (Gl := Gl) e Dw.Ψ φw) (x, i) =
        φw (⟨e.symm x, hxw⟩, i) := fun i => by
      simp [Precedes.restrictφ, transportField, barField, hxw]
    simp only [e3]
    exact hEL.2 ⟨e.symm x, hxw⟩

end TransportEL

end Balaban.Background
