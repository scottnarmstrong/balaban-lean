/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalRepRemoval

/-!
# Region histories that agree up to a scale (transport along `Agree`)

Two region histories `H₁, H₂` that have the same steps `j < m` and the same removal sets `Rem_j`,
`j ≤ m` (`HAgr m`), have the same regions `Z^pre_j`, `j ≤ m`, hence the same components, and the
objects defined from the records up to the scale `j ≤ m` correspond under the identification of the
components with the same set of cubes (`HAgr.cequiv`): the parts, the new and outer cubes, the
spines and books, the localized histories (`Spine/AgreeTransportKappa.lean`).

* `HAgr.of_agree`: `A.Agree k (k+1) B` gives `HAgr k A.H B.H`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

/-- The components of two equal regions are identified (at the level of the finite sets). -/
noncomputable def compsEquiv {ω d L : ℕ} {Z₁ Z₂ : Finset (Torus d L)} (e : Z₁ = Z₂) :
    ↥(comps ω Z₁) ≃ ↥(comps ω Z₂) :=
  Equiv.subtypeEquivRight fun Y => by rw [e]

theorem compsEquiv_val {ω d L : ℕ} {Z₁ Z₂ : Finset (Torus d L)} (e : Z₁ = Z₂) (c : ↥(comps ω Z₁)) :
    (compsEquiv e c).1 = c.1 := rfl

/-- **Agreement of two region histories up to the scale `m`**: the same steps `j < m` and the same
removal sets `Rem_j`, `j ≤ m`. -/
structure HAgr (m : ℕ) (H₁ H₂ : RegionHistory S n R k0 K) : Prop where
  step : ∀ j, j < m → H₁.step j = H₂.step j
  rem : ∀ j, j ≤ m → H₁.rem j = H₂.rem j

/-- Histories that agree up to `k` with the `R`-records up to `k` agree as region histories. -/
theorem HAgr.of_agree {k : ℕ} {A B : LabHist S n R k0 K} (h : A.Agree k (k + 1) B) :
    HAgr k A.H B.H := by
  refine ⟨fun j hj => ?_, fun j hj => (h.2 j (by omega)).1⟩
  obtain ⟨hP, hQ, hR, hS⟩ := h.1 j hj
  exact regionStep_ext (LabHist.Agree.region_eq (Nat.lt_succ_self k) h j hj.le) hP hQ hR hS

namespace HAgr

variable {m : ℕ} {H₁ H₂ : RegionHistory S n R k0 K} (h : HAgr m H₁ H₂)
include h

theorem zpre : ∀ j, j ≤ m → H₁.F.Zpre j = H₂.F.Zpre j
  | 0, _ => rfl
  | j + 1, hj => by
    show (H₁.F.step j).Zpre _ _ = (H₂.F.step j).Zpre _ _
    rw [show H₁.F.step j = H₂.F.step j from h.step j (by omega)]

theorem zp {j : ℕ} (hj : j ≤ m) : H₁.F.Zp j = H₂.F.Zp j := by
  show finOf (H₁.F.Zpre j) = finOf (H₂.F.Zpre j)
  rw [h.zpre j hj]

/-- The identification of the components of `H₁` and `H₂` at the scales `j ≤ m`. -/
noncomputable def cequiv {j : ℕ} (hj : j ≤ m) : H₁.Comp j ≃ H₂.Comp j := compsEquiv (h.zp hj)

/-- The component of `H₂` with the same cubes. -/
noncomputable def cmap {j : ℕ} (hj : j ≤ m) (c : H₁.Comp j) : H₂.Comp j := h.cequiv hj c

theorem cmap_val {j : ℕ} (hj : j ≤ m) (c : H₁.Comp j) : (h.cmap hj c).1 = c.1 :=
  compsEquiv_val (h.zp hj) c

theorem cequiv_val {j : ℕ} (hj : j ≤ m) (c : H₁.Comp j) : (h.cequiv hj c).1 = c.1 :=
  compsEquiv_val (h.zp hj) c

theorem mem_parts {j : ℕ} (hj : j + 1 ≤ m) (c : H₁.Comp j) (Z' : H₁.Comp (j + 1)) :
    h.cmap (by omega) c ∈ H₂.parts j (h.cmap hj Z') ↔ c ∈ H₁.parts j Z' := by
  rw [H₂.mem_parts, H₁.mem_parts, ← h.rem j (by omega)]
  simp only [IsSucc, h.cmap_val]

theorem parts_eq {j : ℕ} (hj : j + 1 ≤ m) (Z' : H₁.Comp (j + 1)) :
    H₂.parts j (h.cmap hj Z') = (H₁.parts j Z').map (h.cequiv (by omega)).toEmbedding := by
  ext c
  rw [Finset.mem_map_equiv]
  have this := h.mem_parts hj ((h.cequiv (by omega)).symm c) Z'
  have e : h.cmap (by omega) ((h.cequiv (by omega)).symm c) = c :=
    (h.cequiv (by omega)).apply_symm_apply c
  rw [e] at this
  exact this

theorem newCubes_eq {j : ℕ} (hj : j < m) : H₁.newCubes (j + 1) = H₂.newCubes (j + 1) := by
  show finOf (H₁.step j).newCubes = finOf (H₂.step j).newCubes
  rw [h.step j hj]

theorem outCubes_eq {j : ℕ} (hj : j + 1 ≤ m) (Z' : H₁.Comp (j + 1)) :
    H₂.outCubes j (h.cmap hj Z') = H₁.outCubes j Z' := by
  have hs : H₁.step j = H₂.step j := h.step j (by omega)
  ext x
  simp only [RegionHistory.outCubes, Finset.mem_filter, Finset.mem_univ, true_and, h.cmap_val,
    ← hs]

end HAgr

end Balaban.RootFSpine
