/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatEngineLift
public import Balaban.Fluctuation.MarkedHatRows
public import Balaban.Localization.Decoupled2Analytic
public import Balaban.Localization.DecCover
public import Balaban.SmallField.XiDomOpen

/-!
# Transport of the step's variables to a background generating set

P3 pp. 78-79, (4.44)-(4.47) (P6 §§4.1-4.4) computes each term of the new level with the local
generating set `𝔹_{k+1}(Y)` of its polymer, while the localization expansion itself (its cubes, its
connected families, its labels) is the expansion of the step on the whole-level set `𝔹_{k+1}`, and
the fluctuation variable `ψ̂` is the step's.  The mark, determinant and activity objects of the
step are therefore made generic in a background generating set `Gb`; three maps connect the step's
expansion set `Gp` to `Gb` (four maps):

* `par`: the decoupling parameters of the cubes of `Gb`, from those of `Gp`;
* `lift`: the lift of a field on the unit lattice of `Gb` to the fine torus;
* `res`: the restriction of a hat variable on the unit lattice of `Gp` to that of `Gb`;
* `dat`: the datum of `Gb` read by the term from the raw datum of the step (the parameter `θ` of a
  mark family stays in the step's parameter space; the term reads `dat θ`).

* `BgTransport`: the four maps;
* `BgTransport.self`: `Gb = Gp` for a level set `Gp`, with the identity on the parameters and on
  the hat variable and on the datum and the lift `liftC` (constant on the unit blocks): the instance at which the
  generic objects are the landed step objects (definitionally);
* `BgTransport.canon`: the maps of P3 (4.44)-(4.47) for any `Gb`: a cube of `Gb` based in the top
  layer `Ω_{k+1}(Gb)` keeps the parameter of `Gp` (extended by `1` off its centres), the other cubes
  of `Gb` get `0`; the lift is the extension by zero off the unit blocks of `Gb`; the restriction
  keeps the hat variable at the unit points of `Gb`, and the datum is cut off to the data of `Gb`
  (`clipRawL`).  These are the parameters, the local hat lift
  and the restriction of `coef_eTermFun_replacement_localB` and `zeroSourceTerm_localB_hat`;
* `LabelMargin`: the labels of `Gb`, i.e. those with the margin of the replacement lemma;
  `labelMargin_of_isLevel`: every label qualifies at a level set;
* `markedHatPsiFBg_liftZ_preimage_mask`: the mask of the marked hat field with the extension by zero;
* `BgTransport.canon_eq_self`: for a level set `Gp` the canonical maps from `Gp` to itself are the
  maps of `BgTransport.self`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.LargeField Balaban.Multiscale Balaban.Fluctuation Balaban.Background Balaban.SmallField Finset Matrix

section Transport

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb : ℝ}

/-- **The transport from the step's expansion set `Gp` to a background generating set `Gb`**: the
decoupling parameters of the cubes of `Gb` as a function of those of `Gp` (`par`), the lift of a
field of the unit lattice of `Gb` to the fine torus (`lift`), the restriction of a hat variable
of the unit lattice of `Gp` to that of `Gb` (`res`), and the datum of `Gb` read by the term from the
raw datum of the step (`dat`: the identity for the step's own set, the cut-off `clipRaw Gb` for a
local set). -/
structure BgTransport (Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb) (N : ℕ) where
  /-- The decoupling parameters of the cubes of `Gb`. -/
  par : DecParams Gp → DecParams Gb
  /-- The lift of a field of the unit lattice of `Gb` to the fine torus. -/
  lift : (unitPts Gb × Fin N → ℂ) →ₗ[ℂ] (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
  /-- The restriction of a hat variable of the unit lattice of `Gp` to that of `Gb`. -/
  res : (unitPts Gp × Fin N → ℂ) →ₗ[ℂ] (unitPts Gb × Fin N → ℂ)
  /-- The datum of `Gb` read by the term from the datum of the step. -/
  dat : RawData d L (N₁ * L ^ m₁) (k + 1) N →ₗ[ℂ] RawData d L (N₁ * L ^ m₁) (k + 1) N

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb} {N : ℕ}

/-- **The step's own transport**: for a level set `Gp` (`Ω₁ = 𝕋`, one layer `k + 1`), the
background set is `Gp` itself, the parameters and the hat variable are unchanged and the lift is
`liftC` (constant on the unit blocks). -/
def BgTransport.self (hG' : IsLevel Gp (k + 1)) : BgTransport Gp Gp N where
  par s := s
  lift := liftC hG'
  res := LinearMap.id
  dat := LinearMap.id

@[simp] theorem BgTransport.self_par (hG' : IsLevel Gp (k + 1)) (s : DecParams Gp) :
    (BgTransport.self (N := N) hG').par s = s := rfl

@[simp] theorem BgTransport.self_lift (hG' : IsLevel Gp (k + 1)) :
    (BgTransport.self (N := N) hG').lift = liftC hG' := rfl

@[simp] theorem BgTransport.self_dat (hG' : IsLevel Gp (k + 1))
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) : (BgTransport.self (N := N) hG').dat Θ = Θ := rfl

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
/-- **The cut-off of a raw datum to the data of `Gb`** as a linear map: the first field is kept on
the data sites of `Gb` and the second on the top layer `Ω₁(Gb)`, both set to `0` elsewhere
(`clipRaw Gb`). -/
noncomputable def clipRawL (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb) :
    RawData d L (N₁ * L ^ m₁) (k + 1) N →ₗ[ℂ] RawData d L (N₁ * L ^ m₁) (k + 1) N where
  toFun r := clipRaw Gb r
  map_add' r r' := by
    refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_) <;>
      by_cases h : x ∈ dataSites Gb <;> by_cases h' : x ∈ Gb.Ω 1 <;> simp [clipRaw, h, h']
  map_smul' c r := by
    refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_) <;>
      by_cases h : x ∈ dataSites Gb <;> by_cases h' : x ∈ Gb.Ω 1 <;> simp [clipRaw, h, h']

theorem clipRawL_apply (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb)
    (r : RawData d L (N₁ * L ^ m₁) (k + 1) N) : clipRawL Gb r = clipRaw Gb r := rfl

open Classical in
/-- **The canonical transport to a background set `Gb`** (P3 (4.44)-(4.47)): a cube of `Gb` based
in the top layer `Ω_{k+1}(Gb)` keeps the parameter of `Gp` (extended by `1` off the centres of `Gp`),
the other cubes get `0`; the lift is the extension by zero `liftZ`; the hat variable is restricted
by `resZ`.

The transport is defined for every `Gb`, but it is the transport of the source only for the local
generating set `Gb = localB (k + 1) hk Y⁺ _ = 𝔹_{k+1}(Y)` of a polymer, with the margin `hmar`
(every site within sup-distance `2 M₁ L^{k+1}` of the read region `R` lies in `Ω_{k+1}(𝔹_{k+1}(Y))`).
For such `Gb` the cubes based in the top layer are the cubes of the source's `Y₁` that matter
(P3 p. 79: the parameters are `s` inside `Y₁` and `0` outside), because
`coef_eTermFun_replacement_localB` proves that the coefficient of the term recomputed on `Gb` with
the parameters `par` equals that of the term of the whole-level expansion; "top layer of `Gb`" is
`Y₁` only through that lemma. For other `Gb` no such identity is asserted. -/
noncomputable def BgTransport.canon (Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb) (N : ℕ) : BgTransport Gp Gb N where
  par s P := if P.1.2 ∈ Gb.Ω (k + 1) then Dec2.extS (coverOf Gp) s P.1 else 0
  lift := liftZ Gb
  res := resZ Gp Gb
  dat := clipRawL Gb

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
  · exact LinearMap.ext fun r => clipRaw_of_isLevel hG' r


open Classical in
/-- **The preimage of a mask**: the unit points of `Gb` whose unit block, as a unit point of the
level set `Gp`, lies in the set `Zm` of unit points of `Gp`. -/
noncomputable def maskPre (hG' : IsLevel Gp (k + 1))
    (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb) (Zm : Finset (unitPts Gp)) :
    Finset (unitPts Gb) :=
  Finset.univ.filter fun q => (⟨q.1, mem_unitPts_of_isLevel hG' q.1⟩ : unitPts Gp) ∈ Zm

/-- **The mask of `markedHatPsiFBg` with the extension by zero is the mask on the fine site.**
For `Zb = maskPre hG' Gb Zm`, the marked hat field `markedHatPsiFBg Gb … (liftZ Gb) … Zb` at a site
`x` is `(u + 1[unitPt x ∈ Zm] t)` times the local hat lift of `cc • C^{1/2}_{Gb}(s) ψ̂` (zero off
the unit blocks of `Gb`): the marked form of `LocalClassDensityMarks`. -/
theorem markedHatPsiFBg_liftZ_preimage_mask (hG' : IsLevel Gp (k + 1)) (a₁ ν : ℝ) (cc : ℂ)
    (F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ))
    (Zm : Finset (unitPts Gp)) (u t : ℂ) (s : DecParams Gb)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (ψh : unitPts Gb × Fin N → ℂ)
    (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    markedHatPsiFBg Gb a₁ ν (liftZ Gb) cc F₁ (maskPre hG' Gb Zm) u t s Θ ψh x i =
      (u + if unitPt hG' x ∈ Zm then t else 0) *
        (if h : unitBlock x ∈ unitPts Gb then
          (cc • (hatSqrtF Gb a₁ ν F₁ s Θ *ᵥ ψh)) (⟨unitBlock x, h⟩, i) else 0) := by
  classical
  unfold markedHatPsiFBg
  simp only [Pi.add_apply, Pi.smul_apply, liftZ_apply, smul_eq_mul]
  by_cases h : unitBlock x ∈ unitPts Gb
  · have hm : (⟨unitBlock x, h⟩ : unitPts Gb) ∈ maskPre hG' Gb Zm ↔ unitPt hG' x ∈ Zm := by
      simp only [maskPre, Finset.mem_filter, Finset.mem_univ, true_and]; rfl
    simp only [h, dite_true, maskBlock]
    by_cases hz : unitPt hG' x ∈ Zm
    · simp [hm.2 hz, hz]; ring
    · simp [hz, mt hm.1 hz]
  · simp [h]

/-- **The labels of a background generating set** (P3 pp. 78-79; the margin `hmar` of
`coef_eTermFun_replacement_localB`, `localB_collar_margin`): a label `Y` of the step's expansion is
a label of `Gb` when every site within sup-distance `2 M₁ L^{k+1}` of `Y` lies in the top layer
`Ω_{k+1}(Gb)`; in particular `Y ⊆ Ω_{k+1}(Gb)`.  The clauses (locality, Cauchy bound, analyticity)
of the terms recomputed on `Gb` are statements about these labels only: the cubes of `Gb` outside
the top layer carry the parameter `0`. -/
def LabelMargin (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) : Prop :=
  ∀ x ∈ Y, ∀ y : CTorus d L N₁ m₁ (k + 1), supDist x y ≤ 2 * L ^ (k + 1 + m₁) →
    y ∈ Gb.Ω (k + 1)

theorem LabelMargin.subset {Y : Set (CTorus d L N₁ m₁ (k + 1))} (h : LabelMargin Gb Y) :
    ∀ x ∈ Y, x ∈ Gb.Ω (k + 1) := fun x hx =>
  h x hx x (by rw [supDist_self]; exact Nat.zero_le _)

/-- **At the step's own set every label qualifies**: for a level set `Gp` every site lies in the
top layer, so `LabelMargin Gp Y` holds for every `Y`. -/
theorem labelMargin_of_isLevel (hG' : IsLevel Gp (k + 1)) (Y : Set (CTorus d L N₁ m₁ (k + 1))) :
    LabelMargin Gp Y := fun _ _ y _ => (Gp.mem_layer.1 (hG'.mem_layer y)).1

end Transport

end Balaban.Localization
