/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2Regime
public import Balaban.SmallField.Def6BridgeDomain
public import Balaban.SmallField.XiLevelC
public import Balaban.SmallField.XiSymm
public import Balaban.Symmetry.Rotation
public import Balaban.Localization.DecoupledBackground
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Def-6 v2, part 2: the field domain as a parameter; the pinned domain -- DRAFT

**Draft, pending Roland's answer to Q13** (`notes/phase1/Q13-ANSWER-astra.md`).  CLASS-RULINGS-2
"Lean-ready class interface" and items 4, 5, 7.

The complex field domain of the localized terms is a **parameter** `FieldDom` of the second version
of the classes, so that the decision asked in Q13 is one instantiation:

* `xiFieldDom`: the domain `Ξ^c_j(𝔹; 1, ε_j)` of the landed class (`Def6.XiDom`), no condition on
  the external field beyond `Ξ^c_j`;
* `pinFieldDom hStar rH`: the pinned domain `Pin hStar rH` of CLASS-RULINGS-2 item 4 and
  Q13-ANSWER (3.1): `h = h_* + z`, `h_*` a constant real unit vector, `sup_x ‖z(x)‖ < r_h`, and the
  spin/background inequalities of `Ξ^c_j` over the **pinned real witness** `h₀ = h_*`
  (MASS-LEVEL §4; item 7);
* `pinAllFieldDom rH`: the union of the pinned charts over the real unit `h_*` (item 4, "a compact
  bounded union of such pinned charts"), the `O(N)`-invariant instance.

The birth-level tag `j` is an argument of the domain.  Results:

* `Pin.xiDom` (the pinned domain lies in `Ξ^c_j`), `Pin.vn_lt` (`‖h‖ < B_h = 1 + r_h`, items 4, 5),
  `Pin.mono`;
* `Pin.inPsiTildeCLevel`: **(D1-j)** on the pinned domain, with W130's level-`j` data domain
  `InPsiTildeCLevel` (MASS-LEVEL (D1-j); item 7): the norm clause `r4` is at the mass `ν L^{2j}`
  and vanishes at the pinned unit witness (`Pin.r4_eq_zero`);
* `pin_of_close`, `Pin.rot`, `pin_const_unit`: configurations close to a coordinate vector, real
  `O(N)`-covariance, and **the constant real unit data of the frozen root lie in the pinned
  domain** (`pin_const_unit`, `frozenRoot_field_mem_pin`; items "Ruling", 5).
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Finset Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-! ### The field domain as a parameter -/

/-- **The field domain of a class member on one torus** (CLASS-RULINGS-2, "Lean-ready class
interface"; the parameter in which the Q13 decision is one instantiation):
* `phys`: the real external fields `h₀` at which the density identity (H.1) is stated ("state the
  density identity on real unit `h`");
* `dom j G`: the complex domain of the data `(Ψ, h)` of the terms **born at level `j`** over the
  generating set `G` (analyticity, bounds, rotation, Euclidean covariance and realness are stated
  on it).
Draft pending Roland's answer to Q13. -/
structure FieldDom (d L N₁ m₁ k N : ℕ) [NeZero L] [NeZero N₁] (ϱ : ℝ) where
  /-- the real external fields of the density identity -/
  phys : Set (Fin N → ℝ)
  /-- the complex domain of the level-`j` terms over a generating set -/
  dom : ℕ → GeneratingSet d L (N₁ * L ^ m₁) k ϱ → Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → Prop

/-- `D'` is contained in `D`: fewer physical fields and smaller complex domains. -/
def FieldDom.Sub (D' D : FieldDom d L N₁ m₁ k N ϱ) : Prop :=
  D'.phys ⊆ D.phys ∧ ∀ j G Ψ h, D'.dom j G Ψ h → D.dom j G Ψ h

/-- **The pinned domain `Pin h_* r_h`** (CLASS-RULINGS-2 items 4, 5, 7; Q13-ANSWER (3.1);
MASS-LEVEL §4) for the level `j`, the generating set `G`, the kernel sequence `a`, the background
mass `μ` and the radius `ε`: complex data `(Ψ, h)` with
* `h_*` a constant **real unit** vector,
* `h = h_* + h''` with `sup_x ‖h''(x)‖ < r_h` (so `‖h‖ < B_h = 1 + r_h`, `Pin.vn_lt`),
* `Ψ = Ψ₀ + Ψ''` and the existing spin/background inequalities: `Ξ^c_j(𝔹; 1, ε)` (landed `XiC`)
  over the real datum `(Ψ₀, h_*)`, i.e. with the real witness of the field **pinned** to `h_*`.
At zero background mass the landed `Ξ^c_j` puts no condition on `h''`; the pin makes the constant
`h`-line finite, so Liouville no longer applies (item 4).  Draft pending Roland's answer to Q13. -/
def Pin (hStar : Fin N → ℝ) (rH : ℝ) (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) (a : ℕ → ℝ)
    (μ : ℝ) (j : ℕ) (ε : ℝ) (Ψ h : Fld d L N₁ m₁ k N) : Prop :=
  ∑ i, hStar i ^ 2 = 1 ∧
    ∃ (Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ) (Ψ'' h'' : CTorus d L N₁ m₁ k → Fin N → ℂ),
      (∀ x i, Ψ x i = (Ψ₀ x i : ℂ) + Ψ'' x i) ∧ (∀ x i, h x i = (hStar i : ℂ) + h'' x i) ∧
        (∀ x, vn (h'' x) < rH) ∧ SmallField.XiC G a μ j 1 ε Ψ₀ hStar Ψ'' h''

/-- **The domain of the landed class** as a field domain: `Ξ^c_j(𝔹; 1, ε_j)` (`Def6.XiDom`) with
kernel sequence `a` and background mass `μ`; the density identity at every real `h₀`. -/
def xiFieldDom (a : ℕ → ℝ) (μ : ℝ) (ε : ℕ → ℝ) : FieldDom d L N₁ m₁ k N ϱ where
  phys := Set.univ
  dom := fun j G Ψ h => XiDom G a μ j (ε j) Ψ h

/-- **The pinned field domain at `h_*`** (CLASS-RULINGS-2 item 4): the density identity at the
real unit field `h_*`, the terms on `Pin h_* r_h`.  Draft pending Roland's answer to Q13. -/
def pinFieldDom (hStar : Fin N → ℝ) (rH : ℝ) (a : ℕ → ℝ) (μ : ℝ) (ε : ℕ → ℝ) :
    FieldDom d L N₁ m₁ k N ϱ where
  phys := {h₀ | h₀ = hStar ∧ ∑ i, h₀ i ^ 2 = 1}
  dom := fun j G Ψ h => Pin hStar rH G a μ j (ε j) Ψ h

/-- **The union of the pinned charts** over the real unit vectors `h_*` (CLASS-RULINGS-2 item 4,
"or a compact bounded union of such pinned charts"): the density identity at every real unit field,
the `O(N)`-invariant instance.  Draft pending Roland's answer to Q13. -/
def pinAllFieldDom (rH : ℝ) (a : ℕ → ℝ) (μ : ℝ) (ε : ℕ → ℝ) : FieldDom d L N₁ m₁ k N ϱ where
  phys := {h₀ | ∑ i, h₀ i ^ 2 = 1}
  dom := fun j G Ψ h => ∃ hStar : Fin N → ℝ, Pin hStar rH G a μ j (ε j) Ψ h

section Basic

variable {hStar : Fin N → ℝ} {rH rH' : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ}
  {μ : ℝ} {j : ℕ} {ε : ℝ} {Ψ hf : Fld d L N₁ m₁ k N}

/-- The pinned domain lies in the domain `Ξ^c_j` of the landed class. -/
theorem Pin.xiDom (h : Pin hStar rH G a μ j ε Ψ hf) : XiDom G a μ j ε Ψ hf := by
  obtain ⟨-, Ψ₀, Ψ'', h'', h1, h2, -, h3⟩ := h
  exact ⟨Ψ₀, hStar, Ψ'', h'', h1, h2, h3⟩

theorem Pin.unit (h : Pin hStar rH G a μ j ε Ψ hf) : ∑ i, hStar i ^ 2 = 1 := h.1

theorem Pin.mono (hr : rH ≤ rH') (h : Pin hStar rH G a μ j ε Ψ hf) :
    Pin hStar rH' G a μ j ε Ψ hf := by
  obtain ⟨hu, Ψ₀, Ψ'', h'', h1, h2, h3, h4⟩ := h
  exact ⟨hu, Ψ₀, Ψ'', h'', h1, h2, fun x => (h3 x).trans_le hr, h4⟩

/-- On the pinned domain `‖h(x) - h_*‖ < r_h`. -/
theorem Pin.vn_sub_lt (h : Pin hStar rH G a μ j ε Ψ hf) (x : CTorus d L N₁ m₁ k) :
    vn (fun i => hf x i - (hStar i : ℂ)) < rH := by
  obtain ⟨-, Ψ₀, Ψ'', h'', -, h2, h3, -⟩ := h
  have e : (fun i => hf x i - (hStar i : ℂ)) = h'' x := funext fun i => by rw [h2 x i]; ring
  rw [e]; exact h3 x

/-- **The field bound of the pinned domain** (CLASS-RULINGS-2 items 4, 5): `‖h(x)‖ < B_h = 1 + r_h`.
In the zero-background branch the landed `Ξ^c` has no such bound. -/
theorem Pin.vn_lt (h : Pin hStar rH G a μ j ε Ψ hf) (x : CTorus d L N₁ m₁ k) :
    vn (hf x) < 1 + rH := by
  have h3 := h.vn_sub_lt x
  have hu := h.unit
  have h1 : vn (fun i => (hStar i : ℂ)) = 1 := by
    rw [vn_ofReal]; unfold rn; rw [hu]; simp
  have t := vn_triangle (hf x) (fun i => (hStar i : ℂ)) 0
  rw [sub_zero, sub_zero, h1] at t
  have e : hf x - (fun i => (hStar i : ℂ)) = fun i => hf x i - (hStar i : ℂ) := rfl
  rw [e] at t
  linarith

/-- The norm clause (R4) of the data domain vanishes at the pinned unit witness, at every level
(MASS-LEVEL §4; CLASS-RULINGS-2 item 7). -/
theorem Pin.r4_eq_zero (h : Pin hStar rH G a μ j ε Ψ hf) (n : ℕ) :
    μ * ((L : ℝ) ^ n) ^ 2 * |∑ i, hStar i ^ 2 - 1| = 0 := by
  rw [h.unit]; simp

/-- **(D1-j) on the pinned domain** (MASS-LEVEL (D1-j); CLASS-RULINGS-2 item 7), with W130's
level-`j` data domain: for a generating set with no active layer above the birth level `j`, the
pinned data lie in `Ψ̃^c_{j|k}(𝔹; C₁ ε, ε)` over the real datum `(Ψ₀, h_*)`. -/
theorem Pin.inPsiTildeCLevel (H : BgHyp d L k ϱ a μ) (hΩ : G.Ω (j + 1) = ∅) (hε1 : ε ≤ 1)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * (1 * ε)) ≤ 1) (h : Pin hStar rH G a μ j ε Ψ hf) :
    ∃ (Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ) (Ψ'' h'' : CTorus d L N₁ m₁ k → Fin N → ℂ),
      (∀ x i, Ψ x i = (Ψ₀ x i : ℂ) + Ψ'' x i) ∧ (∀ x i, hf x i = (hStar i : ℂ) + h'' x i) ∧
        (∀ x, vn (h'' x) < rH) ∧
          InPsiTildeCLevel G μ j (xiC1 d * (1 * ε)) ε Ψ₀ hStar Ψ'' h'' := by
  obtain ⟨-, Ψ₀, Ψ'', h'', h1, h2, h3, h4⟩ := h
  exact ⟨Ψ₀, Ψ'', h'', h1, h2, h3, xiC_subset_psiTildeCLevel H hΩ le_rfl hε1 hsmall h4⟩

/-- **Configurations close to a coordinate vector lie in the pinned domain at it**: a field `Ψ`,
constant on the `j`-blocks, with `|Ψ - e| ≤ ρ`, and a constant `h = c` with
`μ L^{2j} |c - e| ≤ ρ` and `‖c - e‖ < r_h` (the proof of `xiDom_of_close`, whose real witness is
`(e, e)`). -/
theorem pin_of_close (H : BgHyp d L k ϱ a μ) (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k)
    {δ ρ : ℝ} (i₀ : Fin N) (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N)
    (hρ0 : 0 < ρ) (hρ : (N : ℝ) * ρ < δ ^ 2) (hε : (2 * bgK1 d L N + 2) * δ ≤ ε)
    (Ψ : CTorus d L N₁ m₁ k → Fin N → ℂ) (c : Fin N → ℂ)
    (hΨ : ∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ)
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    (hc : ∀ i, μ * ((L : ℝ) ^ j) ^ 2 * ‖c i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ)
    (hpin : vn (fun i => c i - (Pi.single i₀ 1 : Fin N → ℂ) i) < rH) :
    Pin (Pi.single i₀ 1) rH G a μ j ε Ψ (fun _ => c) := by
  have hP := inPsiTildeC_of_close (G := G) hΩ hjk H.mass i₀ hδ0 (hδc0.trans (bgC0_le d L N)) hρ0 hρ
    Ψ c hΨ hΨb hc
  have hK := bgK1_pos d L N
  have hX := psiTildeC_subset_xiC (G := G) (a := a) H hδ0 le_rfl hδc0 hδc1
    (by
      have := H.massLe
      nlinarith [sq_nonneg δ]) hP (εb := ε) (by nlinarith)
  have hX' := xiC_level_irrel (n' := j) (by simp [Pi.single_apply]) hX
  have hu : ∀ i, (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℝ) : ℂ) =
      (Pi.single i₀ 1 : Fin N → ℂ) i := by
    intro i; by_cases h : i = i₀ <;> simp [h]
  refine ⟨by simp [Pi.single_apply], fun _ => Pi.single i₀ 1,
    fun x i => Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i,
    fun _ i => c i - (Pi.single i₀ 1 : Fin N → ℂ) i, fun x i => ?_, fun x i => ?_, fun _ => hpin,
    hX'⟩
  · rw [hu]; ring
  · rw [hu]; ring

/-- **Real `O(N)`-covariance of the pinned domain**: a real orthogonal `Q` maps `Pin h_*` onto
`Pin (Q h_*)` (PIN-I6 §4: "pinning `h_*` must be transported to `R h_*` under rotations"). -/
theorem Pin.rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (h : Pin hStar rH G a μ j ε Ψ hf) :
    Pin (Q *ᵥ hStar) rH G a μ j ε (rotField (cmat Q) Ψ) (rotField (cmat Q) hf) := by
  obtain ⟨hu, Ψ₀, Ψ'', h'', h1, h2, h3, h4⟩ := h
  refine ⟨?_, fun x => Q *ᵥ Ψ₀ x, fun x => cmat Q *ᵥ Ψ'' x, fun x => cmat Q *ᵥ h'' x, ?_, ?_, ?_,
    xiC_rot G a μ hQ h4⟩
  · have := sum_mul_rot_real hQ hStar hStar
    simp only [sq]
    rw [this]
    simpa [sq] using hu
  · intro x i
    have e : Ψ x = (fun l => (Ψ₀ x l : ℂ)) + Ψ'' x := funext fun l => h1 x l
    show (cmat Q *ᵥ Ψ x) i = _
    rw [e, Matrix.mulVec_add, Pi.add_apply, cmat_mulVec]
  · intro x i
    have e : hf x = (fun l => (hStar l : ℂ)) + h'' x := funext fun l => h2 x l
    show (cmat Q *ᵥ hf x) i = _
    rw [e, Matrix.mulVec_add, Pi.add_apply, cmat_mulVec]
  · intro x
    rw [vn_rot (isRealOrth_ofReal hQ)]; exact h3 x

end Basic

/-! ### The data of the frozen root lie in the pinned domain -/

section Frozen

variable {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ} {μ : ℝ} {j : ℕ}

/-- The constant coordinate configuration `(e, e)` lies in the pinned domain at `e`. -/
theorem pin_const_single (H : BgHyp d L k ϱ a μ) (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k)
    {ε rH : ℝ} (hε : 0 < ε) (hr : 0 < rH) (i₀ : Fin N) :
    Pin (Pi.single i₀ 1) rH G a μ j ε (constFld (Pi.single i₀ 1)) (constFld (Pi.single i₀ 1)) := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hK := bgK1_pos d L N
  have hc0 := bgC0_pos d L N hd0
  have hc1 := Balaban.Localization.bgC1_pos' (d := d) (L := L) (N := N) hd0
  set δ := min (min (bgC0 d L N) (bgC1 d L N)) (ε / (2 * bgK1 d L N + 2)) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hc0 hc1) (by positivity)
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos i₀
  have hρ0 : 0 < δ ^ 2 / (2 * N) := by positivity
  have hρ : (N : ℝ) * (δ ^ 2 / (2 * N)) < δ ^ 2 := by
    have e : (N : ℝ) * (δ ^ 2 / (2 * N)) = δ ^ 2 / 2 := by field_simp
    rw [e]; linarith [pow_pos hδ0 2]
  have hε' : (2 * bgK1 d L N + 2) * δ ≤ ε := by
    have h1 : δ ≤ ε / (2 * bgK1 d L N + 2) := min_le_right _ _
    rwa [le_div_iff₀ (by positivity), mul_comm] at h1
  have hz : (fun i => (Pi.single i₀ 1 : Fin N → ℂ) i - (Pi.single i₀ 1 : Fin N → ℂ) i) = 0 := by
    funext i; simp
  have key := pin_of_close (G := G) (rH := rH) H hΩ hjk i₀ hδ0
    ((min_le_left _ _).trans (min_le_left _ _)) ((min_le_left _ _).trans (min_le_right _ _)) hρ0 hρ
    hε' (constFld (Pi.single i₀ 1)) (Pi.single i₀ 1)
    (fun x i => by simpa [constFld] using hρ0.le) (fun _ _ _ => rfl)
    (fun i => by simpa using hρ0.le) (by rw [hz, vn_zero]; exact hr)
  exact key

/-- **The frozen root's data lie in the pinned domain** (CLASS-RULINGS-2 "Ruling": "a fixed real
unit `h` in the frozen root lies in the repaired physical class"; item 5: "for the fixed real unit
field the bound is immediate with `B_h = 1`").  For every real unit vector `h_*` (`N ≥ 2`), the
constant real configuration `(ψ ≡ h_*, h ≡ h_*)` lies in `Pin h_* r_h`, for every level `j ≤ k`,
generating set of level `j`, radius `ε > 0` and pin radius `r_h > 0`. -/
theorem pin_const_unit (H : BgHyp d L k ϱ a μ) (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k)
    {ε rH : ℝ} (hε : 0 < ε) (hr : 0 < rH) {i₀ i₁ : Fin N} (hne : i₀ ≠ i₁) (hStar : Fin N → ℝ)
    (hu : ∑ i, hStar i ^ 2 = 1) :
    Pin hStar rH G a μ j ε (constFld fun i => (hStar i : ℂ)) (constFld fun i => (hStar i : ℂ)) := by
  have hdot : hStar ⬝ᵥ hStar = 1 := by simpa [dotProduct, sq] using hu
  have h0 : hStar ≠ 0 := by
    rintro rfl
    simp [dotProduct] at hdot
  obtain ⟨M, hM, hMh, -⟩ := Balaban.Symmetry.exists_rotation hne hStar hStar h0
  rw [hdot, Real.sqrt_one, one_smul] at hMh
  have hQ : Mᵀᵀ * Mᵀ = 1 := by rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.1 hM
  have hQe : Mᵀ *ᵥ (Pi.single i₀ 1 : Fin N → ℝ) = hStar := by
    rw [← hMh, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
  have base := (pin_const_single (G := G) H hΩ hjk hε hr i₀).rot hQ
  rw [hQe] at base
  have hu' : (fun l => (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) l : ℝ) : ℂ)) =
      (Pi.single i₀ 1 : Fin N → ℂ) := by
    funext l; by_cases h : l = i₀ <;> simp [h]
  have e : rotField (cmat Mᵀ) (constFld (Pi.single i₀ 1 : Fin N → ℂ) : Fld d L N₁ m₁ k N) =
      constFld fun i => (hStar i : ℂ) := by
    funext x i
    show (cmat Mᵀ *ᵥ (Pi.single i₀ 1 : Fin N → ℂ)) i = (hStar i : ℂ)
    rw [← hQe, cmat_mulVec, hu']
  rw [e] at base
  exact base

/-- **Root-F's external field is a physical field of the pinned class**: for the real unit vector
`h` of the frozen root (`‖h‖ = 1` in `EuclideanSpace ℝ (Fin N)`, `N ≥ 2`), `h` is a physical field
of the pinned field domain at `h` (the density identity is stated at it), and the constant data
`(ψ ≡ h, h)` lie in its complex domain at every level. -/
theorem frozenRoot_field_mem_pin (H : BgHyp d L k ϱ a μ) (hΩ : ∀ i, j < i → G.Ω i = ∅)
    (hjk : j ≤ k) {ε : ℕ → ℝ} {rH : ℝ} (hε : 0 < ε j) (hr : 0 < rH) (hN : 2 ≤ N)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1) :
    (fun i => h i) ∈ (pinFieldDom (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ)
        (fun i => h i) rH a μ ε).phys ∧
      (pinFieldDom (fun i => h i) rH a μ ε).dom j G (constFld fun i => ((h i : ℝ) : ℂ))
        (constFld fun i => ((h i : ℝ) : ℂ)) := by
  have hu : ∑ i, (h i) ^ 2 = 1 := by
    have h1 := EuclideanSpace.norm_eq h
    rw [hh] at h1
    have h2 : ∑ i, ‖h i‖ ^ 2 = 1 := by
      have := congrArg (fun t => t ^ 2) h1
      simp only [one_pow] at this
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)] at this
      exact this.symm
    simpa [Real.norm_eq_abs, sq_abs] using h2
  exact ⟨⟨rfl, hu⟩, pin_const_unit H hΩ hjk hε hr
    (i₀ := ⟨0, by omega⟩) (i₁ := ⟨1, by omega⟩) (by simp [Fin.ext_iff]) _ hu⟩

end Frozen

/-! ### Inclusions of the field domains -/

section Sub

variable {a : ℕ → ℝ} {μ : ℝ} {ε : ℕ → ℝ} {rH : ℝ} {hStar : Fin N → ℝ}

/-- The pinned field domain is contained in the domain of the landed class. -/
theorem pinFieldDom_sub_xi :
    (pinFieldDom (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) hStar rH a μ ε).Sub
      (xiFieldDom a μ ε) :=
  ⟨fun _ _ => Set.mem_univ _, fun _ _ _ _ h => h.xiDom⟩

/-- A pinned chart is contained in the union of the pinned charts. -/
theorem pinFieldDom_sub_pinAll :
    (pinFieldDom (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) hStar rH a μ ε).Sub
      (pinAllFieldDom rH a μ ε) :=
  ⟨fun _ h => h.2, fun _ _ _ _ h => ⟨hStar, h⟩⟩

theorem pinAllFieldDom_sub_xi :
    (pinAllFieldDom (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (N := N) (ϱ := ϱ)
      rH a μ ε).Sub (xiFieldDom a μ ε) :=
  ⟨fun _ _ => Set.mem_univ _, fun _ _ _ _ ⟨_, h⟩ => h.xiDom⟩

end Sub

end Balaban.SmallField.Def6v2
