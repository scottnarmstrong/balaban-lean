/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiD1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# (D1), complex data: `Ξ^c_k(𝔹; σ, ε) ⊆ Ψ̃^c(𝔹; δ, ε')`

The complex part of (D1) (P1 Lemma 3.1 for `Ξ^c`), via the difference `F = φ̄^c - φ̄^r` of the two
extensions, which is a smooth field to which `interface_gen` and the block estimates apply.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν σ ε : ℝ}
  {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
  {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {Dr Dc : BgData G N}
  {φr φc : G.Ω 1 × Fin N → ℂ} {αr αc : G.Ω 1 → ℂ}

theorem diffBar_of_mem {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.Ω 1) (i : Fin N) :
    diffBar G Dc.Ψ Dr.Ψ φc φr y i = φc (⟨y, hy⟩, i) - φr (⟨y, hy⟩, i) := by
  simp [diffBar, barVec, barField, hy]

theorem diffBar_of_not_mem {y : Torus d (N₀ * L ^ k)} (hy : y ∉ G.Ω 1) (i : Fin N) :
    diffBar G Dc.Ψ Dr.Ψ φc φr y i = Dc.Ψ y i - Dr.Ψ y i := by
  simp [diffBar, barVec, barField, hy]

theorem xiC_smooth (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1)
    (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc) :
    IsSmoothField G (σ * ε) (diffBar G Dc.Ψ Dr.Ψ φc φr) where
  grad x hx μ := ⟨(hb.grad x hx μ).1.le, (hb.grad x hx μ).2.le⟩
  lap x hx := by
    refine (hb.lap x hx).le.trans ?_
    have hp : 0 < G.spacing x ^ 2 := by have := G.spacing_ge_one x; positivity
    refine div_le_div_of_nonneg_right ?_ hp.le
    nlinarith [mul_pos hσ hε]

/-- The displacement `Ψ''` is the difference of the two data on `Ω₁ ∪ C(Ω₁)`. -/
theorem psi''_eq (hR : Realizes Dr Ψ₀ h₀) (hC : RealizesC Dc Ψ₀ h₀ Ψ'' h'')
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ dataSites G) (i : Fin N) :
    Ψ'' y i = Dc.Ψ y i - Dr.Ψ y i := by
  rw [hC.1 y hy i, hR.1 y hy i]; ring

theorem h''_eq (hR : Realizes Dr Ψ₀ h₀) (hC : RealizesC Dc Ψ₀ h₀ Ψ'' h'')
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.Ω 1) (i : Fin N) :
    h'' y i = Dc.h y i - Dr.h y i := by
  rw [hC.2 y hy i, hR.2 y hy i]; ring

theorem xiC_mean (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) :
    vn (fun i => Ψ'' x i - blockMean G (G.layerIndex x)
      (fun y => diffBar G Dc.Ψ Dr.Ψ φc φr y i) x) < σ ^ 2 * ε := by
  have h := hb.close x hx
  have e : ∀ i, blockAvg G (φc - φr) x i =
      blockMean G (G.layerIndex x) (fun y => diffBar G Dc.Ψ Dr.Ψ φc φr y i) x := fun i => by
    show blockMean G (G.layerIndex x) (fun y => svec G (φc - φr) y i) x = _
    unfold blockMean
    congr 1
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy1 := (blk_mem_Ω1' (precedes_refl G) hx hy).2
    show svec G (φc - φr) y i = diffBar G Dc.Ψ Dr.Ψ φc φr y i
    rw [diffBar_of_mem hy1, svec_of_mem' (φc - φr) hy1]
    rfl
  simp only [e] at h
  exact h

/-- The data of `Ξ^c` unpacked: the pieces used by all the estimates of (D1). -/
theorem xiC_unit (H : BgHyp d L k ϱ a ν) (hDc : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν Dc) :
    ∀ z : G.Ω 1, ∑ i, bgFieldC G a ν (bgC0 d L N) Dc (z, i) *
      bgFieldC G a ν (bgC0 d L N) Dc (z, i) = 1 := by
  obtain ⟨-, hs, -⟩ := theorem72 H hDc
  exact hs.1.2

/-- Sites of the collar have a neighbour in `Ω₁`, at which `F` is `σ ε`-close. -/
theorem xiC_collar_nbr (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1)
    (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ collar G) :
    ∃ y, y ∈ G.Ω 1 ∧ Adj y x ∧
      vn (diffBar G Dc.Ψ Dr.Ψ φc φr x - diffBar G Dc.Ψ Dr.Ψ φc φr y) ≤ σ * ε := by
  obtain ⟨-, y, hy, hadj⟩ := (mem_collar G).1 hx
  refine ⟨y, hy, hadj, ?_⟩
  have hs := xiC_smooth hσ hε hσ1 hb
  have := hs.adj_grad hy hadj
  exact this.trans (div_le_self (mul_pos hσ hε).le (G.spacing_ge_one y))

theorem psi''_collar (hR : Realizes Dr Ψ₀ h₀) (hC : RealizesC Dc Ψ₀ h₀ Ψ'' h'')
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ collar G) :
    Ψ'' x = diffBar G Dc.Ψ Dr.Ψ φc φr x := by
  have hxn : x ∉ G.Ω 1 := ((mem_collar G).1 hx).1
  funext i
  rw [psi''_eq hR hC ((mem_dataSites G).2 (Or.inr hx)) i, diffBar_of_not_mem hxn]

/-- **(D1), complex data, interface** (C1). -/
theorem xiC_c1 (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1)
    (hR : Realizes Dr Ψ₀ h₀) (hC : RealizesC Dc Ψ₀ h₀ Ψ'' h'')
    (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc) {x x' : Torus d (N₀ * L ^ k)}
    (hxx' : IsInterfacePair G x x') :
    vn (Ψ'' x - Ψ'' x') ≤ 2 * (σ ^ 2 * ε + 2 * d * (σ * ε)) + σ * ε := by
  have hs := xiC_smooth hσ hε hσ1 hb
  refine interface_gen (G := G) (f := diffBar G Dc.Ψ Dr.Ψ φc φr) (ψ := Ψ'') (mul_pos hσ hε).le
    (by positivity) hs (fun x hx => (xiC_mean hb hx).le) ?_ ?_ hxx'
  · intro x hx
    exact psi''_collar hR hC hx
  · intro z hz z' hz' hadj
    exact (hb.collarBond z hz z' hz' hadj).le

theorem diffBar_val (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc) {y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.Ω 1) : vn (diffBar G Dc.Ψ Dr.Ψ φc φr y) < ε := by
  have e : diffBar G Dc.Ψ Dr.Ψ φc φr y = fun i => φc (⟨y, hy⟩, i) - φr (⟨y, hy⟩, i) := by
    funext i; exact diffBar_of_mem hy i
  rw [e]; exact hb.val ⟨y, hy⟩

/-- **(D1), complex data, size** (C2a). -/
theorem xiC_size (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1)
    (hR : Realizes Dr Ψ₀ h₀) (hC : RealizesC Dc Ψ₀ h₀ Ψ'' h'')
    (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ dataSites G) : vn (Ψ'' x) < ε + σ * ε + σ ^ 2 * ε := by
  have hA : 0 < σ * ε := mul_pos hσ hε
  have hA2 : 0 ≤ σ ^ 2 * ε := by positivity
  rcases (mem_dataSites G).1 hx with hx1 | hx1
  · have h1 := xiC_mean hb hx1
    obtain ⟨-, hnk, -⟩ := G.layerIndex_spec hx1
    have h2 : vn (fun i => blockMean G (G.layerIndex x) (fun y => diffBar G Dc.Ψ Dr.Ψ φc φr y i) x)
        ≤ ε :=
      vn_blockMean_le (G := G) hnk (diffBar G Dc.Ψ Dr.Ψ φc φr) x
        (fun y hy => (diffBar_val hb (blk_mem_Ω1' (precedes_refl G) hx1 hy).2).le)
    have h3 := vn_le_sub_add (Ψ'' x)
      (fun i => blockMean G (G.layerIndex x) (fun y => diffBar G Dc.Ψ Dr.Ψ φc φr y i) x)
    linarith
  · obtain ⟨y, hy, -, hFy⟩ := xiC_collar_nbr hσ hε hσ1 hb hx1
    rw [psi''_collar hR hC hx1]
    have h3 := vn_le_sub_add (diffBar G Dc.Ψ Dr.Ψ φc φr x) (diffBar G Dc.Ψ Dr.Ψ φc φr y)
    have h4 := diffBar_val hb hy
    have e : (fun i => diffBar G Dc.Ψ Dr.Ψ φc φr x i - diffBar G Dc.Ψ Dr.Ψ φc φr y i) =
        diffBar G Dc.Ψ Dr.Ψ φc φr x - diffBar G Dc.Ψ Dr.Ψ φc φr y := rfl
    rw [e] at h3
    linarith

omit [NeZero N₀] [NeZero L] in
/-- The algebra of (C2b) at a site of `Ω₁`: if `φ·φ = (φ+v)·(φ+v) = 1`, then
`(u+w)² - u²` is controlled by the differences `u - φ`, `w - v`. -/
theorem dot_identity_bound (u w φ v : Fin N → ℂ) {η : ℝ}
    (hid : 2 * ∑ i, φ i * v i + ∑ i, v i * v i = 0)
    (hu : vn (fun i => u i - φ i) ≤ η) (hη : 0 ≤ η) (hw : vn w ≤ 3) (hφ : vn φ ≤ 1)
    (hwv : vn (fun i => w i - v i) ≤ η) (hv : vn v ≤ 1) :
    ‖∑ i, (u i + w i) * (u i + w i) - ∑ i, u i * u i‖ ≤ 12 * η := by
  have key : ∀ i, (u i + w i) * (u i + w i) - u i * u i =
      2 * ((u i - φ i) * w i) + 2 * (φ i * (w i - v i)) + (w i - v i) * (w i + v i) +
        (2 * (φ i * v i) + v i * v i) := fun i => by ring
  have e : ∑ i, (u i + w i) * (u i + w i) - ∑ i, u i * u i =
      2 * ∑ i, (u i - φ i) * w i + 2 * ∑ i, φ i * (w i - v i) + ∑ i, (w i - v i) * (w i + v i) +
        (2 * ∑ i, φ i * v i + ∑ i, v i * v i) := by
    rw [← Finset.sum_sub_distrib]
    simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [e, hid, add_zero]
  have t1 : ‖∑ i, (u i - φ i) * w i‖ ≤ η * 3 :=
    (norm_dot_le _ _).trans (mul_le_mul hu hw (vn_nonneg _) hη)
  have t2 : ‖∑ i, φ i * (w i - v i)‖ ≤ 1 * η :=
    (norm_dot_le _ _).trans (mul_le_mul hφ hwv (vn_nonneg _) zero_le_one)
  have hwv' : vn (fun i => w i + v i) ≤ 4 := by
    have := vn_add' w v
    linarith
  have t3 : ‖∑ i, (w i - v i) * (w i + v i)‖ ≤ η * 4 :=
    (norm_dot_le _ _).trans (mul_le_mul hwv hwv' (vn_nonneg _) hη)
  have n2 : ‖(2 : ℂ)‖ = 2 := by simp
  calc _ ≤ ‖2 * ∑ i, (u i - φ i) * w i‖ + ‖2 * ∑ i, φ i * (w i - v i)‖ +
        ‖∑ i, (w i - v i) * (w i + v i)‖ := norm_add₃_le
    _ ≤ 2 * (η * 3) + 2 * (1 * η) + η * 4 := by
        rw [norm_mul, norm_mul, n2]
        gcongr
    _ = 12 * η := by ring

omit [NeZero N₀] [NeZero L] in
/-- A vector within `e` of a vector of length `≤ M` and square `1` has square `1 + O(e(2M+e))`. -/
theorem dot_sub_one_bound (b φ : Fin N → ℂ) {e M : ℝ} (hφ : ∑ i, φ i * φ i = 1)
    (hb : vn (fun i => b i - φ i) ≤ e) (he : 0 ≤ e) (hM : vn φ ≤ M) :
    ‖∑ i, b i * b i - 1‖ ≤ e * (2 * M + e) := by
  have key : ∀ i, b i * b i - φ i * φ i = (b i - φ i) * (b i - φ i) + 2 * ((b i - φ i) * φ i) :=
    fun i => by ring
  have e1 : ∑ i, b i * b i - 1 = ∑ i, (b i - φ i) * (b i - φ i) + 2 * ∑ i, (b i - φ i) * φ i := by
    rw [← hφ, ← Finset.sum_sub_distrib]
    simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [e1]
  have t1 : ‖∑ i, (b i - φ i) * (b i - φ i)‖ ≤ e * e :=
    (norm_dot_le _ _).trans (mul_le_mul hb hb (vn_nonneg _) he)
  have t2 : ‖∑ i, (b i - φ i) * φ i‖ ≤ e * M :=
    (norm_dot_le _ _).trans (mul_le_mul hb hM (vn_nonneg _) he)
  have n2 : ‖(2 : ℂ)‖ = 2 := by simp
  calc _ ≤ ‖∑ i, (b i - φ i) * (b i - φ i)‖ + ‖2 * ∑ i, (b i - φ i) * φ i‖ := norm_add_le _ _
    _ ≤ e * e + 2 * (e * M) := by
        rw [norm_mul, n2]
        gcongr
    _ = e * (2 * M + e) := by ring

/-- **(C2b) at a site of `Ω₁`.** -/
theorem xiC_c2b_site (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1) (hε1 : ε ≤ 1)
    (hR : Realizes Dr Ψ₀ h₀) (hC : RealizesC Dc Ψ₀ h₀ Ψ'' h'')
    (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc)
    (hφre : ∀ (z : G.Ω 1) i, (φr (z, i)).im = 0)
    (hunr : ∀ z : G.Ω 1, ∑ i, φr (z, i) * φr (z, i) = 1)
    (hunc : ∀ z : G.Ω 1, ∑ i, φc (z, i) * φc (z, i) = 1)
    (hcl : ∀ z : G.Ω 1, vn (fun i => φr (z, i) - Dr.Ψ z i) ≤ xiEta d σ ε)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    ‖∑ i, ((Ψ₀ x i : ℂ) + Ψ'' x i) * ((Ψ₀ x i : ℂ) + Ψ'' x i) -
      ∑ i, (Ψ₀ x i : ℂ) * (Ψ₀ x i : ℂ)‖ ≤ 12 * xiEta d σ ε := by
  have hA : 0 ≤ σ * ε := (mul_pos hσ hε).le
  have hηpos := xiEta_pos (d := d) hσ hε
  have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
  have hs := xiC_smooth hσ hε hσ1 hb
  set φ : Fin N → ℂ := fun i => φr (⟨x, hx⟩, i) with hφdef
  set v : Fin N → ℂ := fun i => φc (⟨x, hx⟩, i) - φr (⟨x, hx⟩, i) with hvdef
  refine dot_identity_bound (fun i => (Ψ₀ x i : ℂ)) (Ψ'' x) φ v ?_ ?_ hηpos.le ?_ ?_ ?_ ?_
  · have h1 := hunc ⟨x, hx⟩
    have h2 := hunr ⟨x, hx⟩
    have e : ∑ i, φc (⟨x, hx⟩, i) * φc (⟨x, hx⟩, i) =
        ∑ i, φ i * φ i + (2 * ∑ i, φ i * v i + ∑ i, v i * v i) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hφdef, hvdef]; ring
    rw [e, h2] at h1
    linear_combination h1
  · have h := hcl ⟨x, hx⟩
    have e : (fun i => (Ψ₀ x i : ℂ) - φ i) = fun i => -(φr (⟨x, hx⟩, i) - Dr.Ψ x i) := by
      funext i; simp [hφdef, hR.1 x hxd i]
    rw [e, vn_neg]; exact h
  · have := xiC_size hσ hε hσ1 hR hC hb hxd
    nlinarith [mul_nonneg hσ.le hε.le, mul_le_mul_of_nonneg_right hσ1 hε.le]
  · have : vn φ = 1 := by
      have e : φ = barVec G Dr.Ψ φr x := by funext i; simp [hφdef, barVec, barField, hx]
      rw [e]; exact barVec_vn_eq_one hφre hunr Dr.Ψ hx
    exact this.le
  · have h1 := psi_sub_le (G := G) (f := diffBar G Dc.Ψ Dr.Ψ φc φr) (ψ := Ψ'') hA hs hx
      (xiC_mean hb hx).le (x_mem_blk (G := G) (G.layerIndex x) x)
    have e : (fun i => Ψ'' x i - v i) = fun i => Ψ'' x i - diffBar G Dc.Ψ Dr.Ψ φc φr x i := by
      funext i; rw [diffBar_of_mem hx]
    rw [e]
    refine h1.trans ?_
    unfold xiEta
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith [mul_pos hσ hε, mul_nonneg this (mul_pos hσ hε).le]
  · have h := diffBar_val hb hx
    have e : diffBar G Dc.Ψ Dr.Ψ φc φr x = v := by funext i; exact diffBar_of_mem hx i
    rw [e] at h
    linarith

/-- **(C2b) at a collar site.** -/
theorem xiC_c2b_collar (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1) (hε1 : ε ≤ 1)
    (hR : Realizes Dr Ψ₀ h₀) (hC : RealizesC Dc Ψ₀ h₀ Ψ'' h'')
    (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc)
    (hφre : ∀ (z : G.Ω 1) i, (φr (z, i)).im = 0)
    (hunr : ∀ z : G.Ω 1, ∑ i, φr (z, i) * φr (z, i) = 1)
    (hunc : ∀ z : G.Ω 1, ∑ i, φc (z, i) * φc (z, i) = 1)
    (hsr : IsSmoothField G (σ * ε) (barVec G Dr.Ψ φr))
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ collar G) :
    ‖∑ i, ((Ψ₀ x i : ℂ) + Ψ'' x i) * ((Ψ₀ x i : ℂ) + Ψ'' x i) -
      ∑ i, (Ψ₀ x i : ℂ) * (Ψ₀ x i : ℂ)‖ ≤ 15 * (σ * ε) := by
  have hA : 0 ≤ σ * ε := (mul_pos hσ hε).le
  have hA1 : σ * ε ≤ 1 := by nlinarith [mul_le_mul hσ1 hε1 hε.le zero_le_one]
  have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inr hx)
  have hxn : x ∉ G.Ω 1 := ((mem_collar G).1 hx).1
  obtain ⟨y, hy, hadj, hFy⟩ := xiC_collar_nbr hσ hε hσ1 hb hx
  have hrn : vn (barVec G Dr.Ψ φr x - barVec G Dr.Ψ φr y) ≤ σ * ε := by
    have := hsr.adj_grad hy hadj
    exact this.trans (div_le_self hA (G.spacing_ge_one y))
  have hφry : (fun i => φr (⟨y, hy⟩, i)) = barVec G Dr.Ψ φr y := by
    funext i; simp [barVec, barField, hy]
  have hφcy : (fun i => φc (⟨y, hy⟩, i)) = barVec G Dc.Ψ φc y := by
    funext i; simp [barVec, barField, hy]
  have hbc : ∀ z, barVec G Dc.Ψ φc z = barVec G Dr.Ψ φr z + diffBar G Dc.Ψ Dr.Ψ φc φr z := by
    intro z; funext i; simp [diffBar]
  -- real
  have hreal : ‖∑ i, Dr.Ψ x i * Dr.Ψ x i - 1‖ ≤ (σ * ε) * (2 * 1 + σ * ε) := by
    refine dot_sub_one_bound (Dr.Ψ x) (fun i => φr (⟨y, hy⟩, i)) (hunr ⟨y, hy⟩) ?_ hA ?_
    · have e : (fun i => Dr.Ψ x i - φr (⟨y, hy⟩, i)) =
          barVec G Dr.Ψ φr x - barVec G Dr.Ψ φr y := by
        funext i; simp [barVec, barField, hxn, hy]
      rw [e]; exact hrn
    · rw [hφry]; exact (barVec_vn_eq_one hφre hunr Dr.Ψ hy).le
  -- complex
  have hnorm_c : vn (barVec G Dc.Ψ φc x - barVec G Dc.Ψ φc y) ≤ 2 * (σ * ε) := by
    rw [hbc x, hbc y]
    have e : (barVec G Dr.Ψ φr x + diffBar G Dc.Ψ Dr.Ψ φc φr x) -
        (barVec G Dr.Ψ φr y + diffBar G Dc.Ψ Dr.Ψ φc φr y) =
        (fun i => (barVec G Dr.Ψ φr x - barVec G Dr.Ψ φr y) i +
          (diffBar G Dc.Ψ Dr.Ψ φc φr x - diffBar G Dc.Ψ Dr.Ψ φc φr y) i) := by
      funext i; simp only [Pi.sub_apply, Pi.add_apply]; ring
    rw [e]
    have := vn_add' (barVec G Dr.Ψ φr x - barVec G Dr.Ψ φr y)
      (diffBar G Dc.Ψ Dr.Ψ φc φr x - diffBar G Dc.Ψ Dr.Ψ φc φr y)
    linarith
  have hMc : vn (fun i => φc (⟨y, hy⟩, i)) ≤ 2 := by
    rw [hφcy, hbc y]
    have := vn_add' (barVec G Dr.Ψ φr y) (diffBar G Dc.Ψ Dr.Ψ φc φr y)
    have h1 := barVec_vn_eq_one hφre hunr Dr.Ψ hy
    have h2 := diffBar_val hb hy
    have e : (barVec G Dr.Ψ φr y + diffBar G Dc.Ψ Dr.Ψ φc φr y) =
        (fun i => barVec G Dr.Ψ φr y i + diffBar G Dc.Ψ Dr.Ψ φc φr y i) := rfl
    rw [e]; linarith
  have hcomp : ‖∑ i, Dc.Ψ x i * Dc.Ψ x i - 1‖ ≤ (2 * (σ * ε)) * (2 * 2 + 2 * (σ * ε)) := by
    refine dot_sub_one_bound (Dc.Ψ x) (fun i => φc (⟨y, hy⟩, i)) (hunc ⟨y, hy⟩) ?_ (by positivity)
      hMc
    have e : (fun i => Dc.Ψ x i - φc (⟨y, hy⟩, i)) =
        barVec G Dc.Ψ φc x - barVec G Dc.Ψ φc y := by
      funext i; simp [barVec, barField, hxn, hy]
    rw [e]; exact hnorm_c
  have e1 : ∑ i, ((Ψ₀ x i : ℂ) + Ψ'' x i) * ((Ψ₀ x i : ℂ) + Ψ'' x i) =
      ∑ i, Dc.Ψ x i * Dc.Ψ x i := by
    refine Finset.sum_congr rfl fun i _ => ?_; rw [hC.1 x hxd i]
  have e2 : ∑ i, (Ψ₀ x i : ℂ) * (Ψ₀ x i : ℂ) = ∑ i, Dr.Ψ x i * Dr.Ψ x i := by
    refine Finset.sum_congr rfl fun i _ => ?_; rw [hR.1 x hxd i]
  rw [e1, e2]
  have e3 : ∑ i, Dc.Ψ x i * Dc.Ψ x i - ∑ i, Dr.Ψ x i * Dr.Ψ x i =
      (∑ i, Dc.Ψ x i * Dc.Ψ x i - 1) - (∑ i, Dr.Ψ x i * Dr.Ψ x i - 1) := by ring
  rw [e3]
  refine (norm_sub_le _ _).trans ?_
  nlinarith

omit [NeZero N₀] [NeZero L] in
theorem vn_normalize_sub (Ψ : Fin N → ℝ) (hr : 0 < rn Ψ) :
    vn (fun i => ((Ψ i / rn Ψ : ℝ) : ℂ) - (Ψ i : ℂ)) = |1 - rn Ψ| := by
  have e : (fun i => ((Ψ i / rn Ψ : ℝ) : ℂ) - (Ψ i : ℂ)) =
      fun i => (((1 / rn Ψ - 1 : ℝ)) : ℂ) * (Ψ i : ℂ) := by
    funext i; push_cast; field_simp
  rw [e, vn_smul_real, vn_ofReal]
  rw [show 1 / rn Ψ - 1 = (1 - rn Ψ) / rn Ψ by field_simp, abs_div, abs_of_pos hr]
  field_simp

/-- **(C3b)**: `ν ℓ² |ψ₀ · h'| < δ²` at a site of `Ω₁`, `ψ₀ = Ψ / |Ψ|`. -/
theorem xiC_c3b (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1) (hν : 0 ≤ ν)
    (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc)
    (hcl : ∀ z : G.Ω 1, vn (fun i => φr (z, i) - Dr.Ψ z i) ≤ xiEta d σ ε)
    (hR : Realizes Dr Ψ₀ h₀) {δ' : ℝ} (hδ : (2 * d + 5) * xiEta d σ ε ≤ δ')
    (hr2 : ∀ x ∈ G.Ω 1, |rn (Ψ₀ x) ^ 2 - 1| ≤ (2 * d + 3) * xiEta d σ ε)
    (hsmall : (4 * d + 6) * xiEta d σ ε ≤ 1)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
      ‖∑ i, ((Ψ₀ x i / rn (Ψ₀ x) : ℝ) : ℂ) * h'' x i‖ < δ' ^ 2 := by
  have hηpos := xiEta_pos (d := d) hσ hε
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
  set η := xiEta d σ ε with hη
  have hση : σ * ε ≤ η := le_xiEta hσ hε
  have hσ2 : σ ^ 2 * ε ≤ σ * ε := by nlinarith [mul_pos hσ hε]
  have hr := hr2 x hx
  have hr0 := rn_nonneg (Ψ₀ x)
  have hsq : 1 / 2 ≤ rn (Ψ₀ x) ^ 2 := by
    have := (abs_le.1 hr).1
    nlinarith
  have hrpos : 0 < rn (Ψ₀ x) := by
    rcases hr0.eq_or_lt with h | h
    · rw [← h] at hsq; norm_num at hsq
    · exact h
  set r := rn (Ψ₀ x) with hrdef
  have h1r : |1 - r| ≤ (2 * d + 3) * η := by
    have h2 : |1 - r ^ 2| = |1 - r| * (1 + r) := by
      rw [show 1 - r ^ 2 = (1 - r) * (1 + r) by ring, abs_mul,
        abs_of_pos (show (0 : ℝ) < 1 + r by linarith)]
    have h3 : |1 - r ^ 2| ≤ (2 * d + 3) * η := by rwa [abs_sub_comm]
    nlinarith [abs_nonneg (1 - r)]
  set u : Fin N → ℂ := fun i => ((Ψ₀ x i / r : ℝ) : ℂ) with hu
  set φ : Fin N → ℂ := fun i => φr (⟨x, hx⟩, i) with hφ
  have hΨc : (fun i => (Ψ₀ x i : ℂ)) = Dr.Ψ x := by funext i; exact (hR.1 x hxd i).symm
  have hdist : vn (fun i => u i - φ i) ≤ (2 * d + 4) * η := by
    have t := vn_tri u (fun i => (Ψ₀ x i : ℂ)) φ
    have e1 : vn (fun i => u i - (Ψ₀ x i : ℂ)) = |1 - r| := vn_normalize_sub (Ψ₀ x) hrpos
    have e2 : vn (fun i => (Ψ₀ x i : ℂ) - φ i) ≤ η := by
      have h := hcl ⟨x, hx⟩
      have e : (fun i => (Ψ₀ x i : ℂ) - φ i) = fun i => -(φr (⟨x, hx⟩, i) - Dr.Ψ x i) := by
        funext i; simp [hφ, hR.1 x hxd i]
      rw [e, vn_neg]; exact h
    linarith
  have hAbs := hb.hAbs x hx
  have hDot := hb.hDot ⟨x, hx⟩
  have hc0 : 0 ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 := by positivity
  have hsplit : ∑ i, u i * h'' x i = ∑ i, φ i * h'' x i + ∑ i, (u i - φ i) * h'' x i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  have hdot2 : ‖∑ i, (u i - φ i) * h'' x i‖ ≤ ((2 * d + 4) * η) * vn (h'' x) :=
    (norm_dot_le _ _).trans (mul_le_mul hdist le_rfl (vn_nonneg _) (by positivity))
  have hε2 : (σ * ε) ^ 2 / ε = σ ^ 2 * ε := by field_simp
  rw [hε2] at hAbs
  have key : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * ‖∑ i, u i * h'' x i‖ <
      (σ * ε) ^ 2 + ((2 * d + 4) * η) * (σ ^ 2 * ε) := by
    rw [hsplit]
    calc ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * ‖∑ i, φ i * h'' x i + ∑ i, (u i - φ i) * h'' x i‖
        ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
          (‖∑ i, φ i * h'' x i‖ + ‖∑ i, (u i - φ i) * h'' x i‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hc0
      _ = ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * ‖∑ i, φ i * h'' x i‖ +
          ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * ‖∑ i, (u i - φ i) * h'' x i‖ := by ring
      _ < (σ * ε) ^ 2 + ((2 * d + 4) * η) * (σ ^ 2 * ε) := by
          have h5 : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * ‖∑ i, (u i - φ i) * h'' x i‖ ≤
              ((2 * d + 4) * η) * (ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h'' x)) := by
            calc _ ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * (((2 * d + 4) * η) * vn (h'' x)) :=
                  mul_le_mul_of_nonneg_left hdot2 hc0
              _ = _ := by ring
          have h6 : ((2 * d + 4) * η) * (ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h'' x)) ≤
              ((2 * d + 4) * η) * (σ ^ 2 * ε) :=
            mul_le_mul_of_nonneg_left hAbs.le (by positivity)
          linarith
  refine key.trans_le ?_
  have h7 : ((2 * d + 4) * η) * (σ ^ 2 * ε) ≤ ((2 * d + 4) * η) * η :=
    mul_le_mul_of_nonneg_left (hσ2.trans hση) (by positivity)
  have h8 : (σ * ε) ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (mul_pos hσ hε).le hση 2
  have h9 : ((2 * d + 5) * η) ≤ δ' := hδ
  have h10 : η ^ 2 + ((2 * d + 4) * η) * η = (2 * d + 5) * η * η := by ring
  have h11 : (2 * d + 5) * η * η ≤ δ' ^ 2 := by
    have h1 : 1 ≤ (2 * (d : ℝ) + 5) := by nlinarith
    calc (2 * (d : ℝ) + 5) * η * η ≤ (2 * (d : ℝ) + 5) * η * η * (2 * (d : ℝ) + 5) :=
          le_mul_of_one_le_right (by positivity) h1
      _ = ((2 * (d : ℝ) + 5) * η) ^ 2 := by ring
      _ ≤ δ' ^ 2 := pow_le_pow_left₀ (by positivity) h9 2
  linarith

/-- **(D1), complex data** (P1 Lemma 3.1 for `Ξ^c` at `λ = ∞`): `Ξ^c_k(𝔹; σ, ε)` lies in the
complex data domain `Ψ̃^c(𝔹; δ', ε'')` for every `δ' ≥ C₄ η`, `ε'' ≥ ε` with
`(σ ε)² / ε ≤ δ'² / ε''`; here `η = (2d+1) σ ε`, `C₄ = 4d + 8`, `σ, ε ≤ 1`,
`(4d+6) η ≤ 1`. -/
theorem xiC_inPsiTildeC (H : BgHyp d L k ϱ a ν) (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1)
    (hε1 : ε ≤ 1) (hsmall : (4 * d + 6) * xiEta d σ ε ≤ 1) {δ' ε'' : ℝ}
    (hδ : compC4 d * xiEta d σ ε ≤ δ') (hεε : ε ≤ ε'') (hrat : (σ * ε) ^ 2 / ε ≤ δ' ^ 2 / ε'')
    (hX : XiC G a ν k σ ε Ψ₀ h₀ Ψ'' h'') : InPsiTildeC G ν δ' ε'' Ψ₀ h₀ Ψ'' h'' := by
  obtain ⟨-, -, Dr, Dc, hXr, hC, hDc, hb⟩ := hX
  have hXr' := hXr
  obtain ⟨hR, hDomR, hbr⟩ := hXr
  have hηpos : 0 < xiEta d σ ε := xiEta_pos hσ hε
  have hση : σ * ε ≤ xiEta d σ ε := le_xiEta hσ hε
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hC4 : compC4 d * xiEta d σ ε = (4 * d + 8) * xiEta d σ ε := rfl
  have hδ' : (4 * (d : ℝ) + 8) * xiEta d σ ε ≤ δ' := by rw [← hC4]; exact hδ
  have hε'' : 0 < ε'' := hε.trans_le hεε
  have hA : 0 < σ * ε := mul_pos hσ hε
  have hσ2 : σ ^ 2 * ε ≤ σ * ε := by nlinarith
  obtain ⟨hφre, hunr⟩ := xi_unit H hXr'
  have hunc := xiC_unit H hDc
  have hcl := (xi_fieldBounds H hσ hε hσ1 hXr').close
  have hsr := xi_smooth hσ hε hσ1 hbr
  have hr2 := fun x (hx : x ∈ G.Ω 1) => xi_r2_site H hσ hε hσ1 hsmall hXr' hx
  have hreal := (xi_inPsiTilde H hσ hε hσ1 hsmall hXr').mono (mul_nonneg (by unfold compC4; positivity) hηpos.le) hδ
  refine ⟨hreal, hε'', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- layer constancy of Ψ''
    intro n hn1 hnk x hx x' hx'
    have hxΩ : x ∈ G.Ω 1 := G.layer_subset hn1 hnk hx
    have hx'l : x' ∈ G.layer n := (G.mem_layer_iff hn1 hnk (GeneratingSet.mem_blk.1 hx')).2 hx
    have hx'Ω : x' ∈ G.Ω 1 := G.layer_subset hn1 hnk hx'l
    funext i
    rw [psi''_eq hR hC ((mem_dataSites G).2 (Or.inl hx'Ω)) i,
      psi''_eq hR hC ((mem_dataSites G).2 (Or.inl hxΩ)) i,
      congrFun (Dc.Ψ_layerConst n hn1 hnk x hx x' hx') i,
      congrFun (Dr.Ψ_layerConst n hn1 hnk x hx x' hx') i]
  · -- layer constancy of h''
    intro n hn1 hnk x hx x' hx'
    have hxΩ : x ∈ G.Ω 1 := G.layer_subset hn1 hnk hx
    have hx'l : x' ∈ G.layer n := (G.mem_layer_iff hn1 hnk (GeneratingSet.mem_blk.1 hx')).2 hx
    have hx'Ω : x' ∈ G.Ω 1 := G.layer_subset hn1 hnk hx'l
    funext i
    rw [h''_eq hR hC hx'Ω i, h''_eq hR hC hxΩ i,
      congrFun (Dc.h_layerConst n hn1 hnk x hx x' hx') i,
      congrFun (Dr.h_layerConst n hn1 hnk x hx x' hx') i]
  · -- (C1)
    intro x x' hxx'
    have h1 := xiC_c1 hσ hε hσ1 hR hC hb hxx'
    refine h1.trans_lt (lt_of_lt_of_le ?_ hδ')
    unfold xiEta
    nlinarith [mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hA.le]
  · -- (C2a)
    intro x hx
    have h1 := xiC_size hσ hε hσ1 hR hC hb hx
    refine h1.trans_le ?_
    nlinarith
  · -- (C2b)
    intro x hx
    rcases (mem_dataSites G).1 hx with hx1 | hx1
    · have := xiC_c2b_site hσ hε hσ1 hε1 hR hC hb hφre hunr hunc hcl hx1
      refine this.trans_lt (lt_of_lt_of_le ?_ hδ')
      nlinarith
    · have := xiC_c2b_collar hσ hε hσ1 hε1 hR hC hb hφre hunr hunc hsr hx1
      refine this.trans_lt (lt_of_lt_of_le ?_ hδ')
      nlinarith
  · -- (C3a)
    intro x hx
    exact (hb.hAbs x hx).trans_le hrat
  · -- (C3b)
    intro x hx
    refine xiC_c3b hσ hε hσ1 H.mass hb hcl hR ?_ hr2 hsmall hx
    nlinarith

end Balaban.SmallField
