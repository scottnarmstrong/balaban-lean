/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatEngineLift
public import Balaban.Localization.Decoupled2Analytic
public import Balaban.Localization.DecCover

/-!
# Transport of the step's variables to a background generating set

P3 pp. 78-79, (4.44)-(4.47) (P6 §§4.1-4.4) computes each term of the new level with the local
generating set `𝔹_{k+1}(Y)` of its polymer, while the localization expansion itself (its cubes, its
connected families, its labels) is the expansion of the step on the whole-level set `𝔹_{k+1}`, and
the fluctuation variable `ψ̂` is the step's.  The mark, determinant and activity objects of the
step are therefore made generic in a background generating set `Gb`; three maps connect the step's
expansion set `Gp` to `Gb`:

* `par`: the decoupling parameters of the cubes of `Gb`, from those of `Gp`;
* `lift`: the lift of a field on the unit lattice of `Gb` to the fine torus;
* `res`: the restriction of a hat variable on the unit lattice of `Gp` to that of `Gb`.

* `BgTransport`: the three maps;
* `BgTransport.self`: `Gb = Gp` for a level set `Gp`, with the identity on the parameters and on
  the hat variable and the lift `liftC` (constant on the unit blocks): the instance at which the
  generic objects are the landed step objects (definitionally);
* `BgTransport.canon`: the maps of P3 (4.44)-(4.47) for any `Gb`: a cube of `Gb` based in the top
  layer `Ω_{k+1}(Gb)` keeps the parameter of `Gp` (extended by `1` off its centres), the other cubes
  of `Gb` get `0`; the lift is the extension by zero off the unit blocks of `Gb`; the restriction
  keeps the hat variable at the unit points of `Gb`.  These are the parameters, the local hat lift
  and the restriction of `coef_eTermFun_replacement_localB` and `zeroSourceTerm_localB_hat`;
* `BgTransport.canon_eq_self`: for a level set `Gp` the canonical maps from `Gp` to itself are the
  maps of `BgTransport.self`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Fluctuation Finset

section Transport

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb : ℝ}

/-- **The transport from the step's expansion set `Gp` to a background generating set `Gb`**: the
decoupling parameters of the cubes of `Gb` as a function of those of `Gp` (`par`), the lift of a
field of the unit lattice of `Gb` to the fine torus (`lift`), and the restriction of a hat variable
of the unit lattice of `Gp` to that of `Gb` (`res`). -/
structure BgTransport (Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb) (N : ℕ) where
  /-- The decoupling parameters of the cubes of `Gb`. -/
  par : DecParams Gp → DecParams Gb
  /-- The lift of a field of the unit lattice of `Gb` to the fine torus. -/
  lift : (unitPts Gb × Fin N → ℂ) →ₗ[ℂ] (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
  /-- The restriction of a hat variable of the unit lattice of `Gp` to that of `Gb`. -/
  res : (unitPts Gp × Fin N → ℂ) →ₗ[ℂ] (unitPts Gb × Fin N → ℂ)

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb} {N : ℕ}

/-- **The step's own transport**: for a level set `Gp` (`Ω₁ = 𝕋`, one layer `k + 1`), the
background set is `Gp` itself, the parameters and the hat variable are unchanged and the lift is
`liftC` (constant on the unit blocks). -/
def BgTransport.self (hG' : IsLevel Gp (k + 1)) : BgTransport Gp Gp N where
  par s := s
  lift := liftC hG'
  res := LinearMap.id

@[simp] theorem BgTransport.self_par (hG' : IsLevel Gp (k + 1)) (s : DecParams Gp) :
    (BgTransport.self (N := N) hG').par s = s := rfl

@[simp] theorem BgTransport.self_lift (hG' : IsLevel Gp (k + 1)) :
    (BgTransport.self (N := N) hG').lift = liftC hG' := rfl

@[simp] theorem BgTransport.self_res (hG' : IsLevel Gp (k + 1))
    (ψh : unitPts Gp × Fin N → ℂ) : (BgTransport.self (N := N) hG').res ψh = ψh := rfl

open Classical in
/-- **The extension by zero** of a field of the unit lattice of `Gb` to the fine torus: the value
at a site is that of its unit block when the block is a unit point of `Gb`, and `0` otherwise. -/
noncomputable def liftZ (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb) :
    (unitPts Gb × Fin N → ℂ) →ₗ[ℂ] (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) where
  toFun v x i := if h : unitBlock x ∈ unitPts Gb then v (⟨unitBlock x, h⟩, i) else 0
  map_add' v w := by
    funext x i
    by_cases h : unitBlock x ∈ unitPts Gb <;> simp [h]
  map_smul' c v := by
    funext x i
    by_cases h : unitBlock x ∈ unitPts Gb <;> simp [h]

theorem liftZ_apply (v : unitPts Gb × Fin N → ℂ) (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    liftZ Gb v x i = if h : unitBlock x ∈ unitPts Gb then v (⟨unitBlock x, h⟩, i) else 0 := rfl

open Classical in
/-- **The restriction of a hat variable** of the unit lattice of `Gp` to that of `Gb`: the value at
a unit point of `Gb` that is a unit point of `Gp`, and `0` at the others. -/
noncomputable def resZ (Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb) :
    (unitPts Gp × Fin N → ℂ) →ₗ[ℂ] (unitPts Gb × Fin N → ℂ) where
  toFun ψh p := if hp : p.1.1 ∈ unitPts Gp then ψh (⟨p.1.1, hp⟩, p.2) else 0
  map_add' v w := by
    funext p
    by_cases h : p.1.1 ∈ unitPts Gp <;> simp [h]
  map_smul' c v := by
    funext p
    by_cases h : p.1.1 ∈ unitPts Gp <;> simp [h]

theorem resZ_apply (ψh : unitPts Gp × Fin N → ℂ) (p : unitPts Gb × Fin N) :
    resZ (N := N) Gp Gb ψh p = if hp : p.1.1 ∈ unitPts Gp then ψh (⟨p.1.1, hp⟩, p.2) else 0 :=
  rfl

open Classical in
/-- **The canonical transport to a background set `Gb`** (P3 (4.44)-(4.47)): a cube of `Gb` based
in the top layer `Ω_{k+1}(Gb)` keeps the parameter of `Gp` (extended by `1` off the centres of `Gp`),
the other cubes get `0`; the lift is the extension by zero `liftZ`; the hat variable is restricted
by `resZ`. -/
noncomputable def BgTransport.canon (Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb) (N : ℕ) : BgTransport Gp Gb N where
  par s P := if P.1.2 ∈ Gb.Ω (k + 1) then Dec2.extS (coverOf Gp) s P.1 else 0
  lift := liftZ Gb
  res := resZ Gp Gb

/-- Every unit block is the block of a site. -/
theorem exists_unitBlock_eq (b : UnitTorus d L N₁ m₁ k) :
    ∃ x : CTorus d L N₁ m₁ (k + 1), unitBlock x = b := by
  have hpos : 0 < (blockFibre (d := d) (ℓ := N₁ * L ^ m₁ * L ^ (k + 1)) (L ^ k)
      ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) b).card := by
    rw [card_blockFibre unitBlock_side]
    exact pow_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _) _
  obtain ⟨x, hx⟩ := Finset.card_pos.1 hpos
  exact ⟨x, mem_blockFibre.1 hx⟩

/-- Every unit block is a unit point of a level set. -/
theorem mem_unitPts_of_isLevel (hG' : IsLevel Gp (k + 1)) (b : UnitTorus d L N₁ m₁ k) :
    b ∈ unitPts Gp := by
  obtain ⟨x, hx⟩ := exists_unitBlock_eq (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) b
  exact (mem_unitPts Gp).2 ⟨x, hG'.mem_layer x, hx⟩

/-- **At a level set the canonical transport is the step's own transport.** -/
theorem BgTransport.canon_eq_self (hG' : IsLevel Gp (k + 1)) :
    BgTransport.canon Gp Gp N = BgTransport.self hG' := by
  classical
  unfold BgTransport.canon BgTransport.self
  congr 1
  · funext s P
    have hP : P.1.2 ∈ Gp.Ω (k + 1) := (Gp.mem_layer.1 (hG'.mem_layer P.1.2)).1
    rw [ite_eq_left hP]
    unfold Dec2.extS
    rw [dite_eq_left (show (P : ℕ × CTorus d L N₁ m₁ (k + 1)) ∈ (coverOf Gp).cubeIdx from P.2)]
    rfl
  · refine LinearMap.ext fun v => ?_
    funext x i
    rw [liftZ_apply, dite_eq_left (mem_unitPts_of_isLevel hG' (unitBlock x)), liftC_apply]
    rfl
  · refine LinearMap.ext fun ψh => ?_
    funext p
    rw [resZ_apply, dite_eq_left p.1.2]
    rfl

end Transport

end Balaban.Localization
