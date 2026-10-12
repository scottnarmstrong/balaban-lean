module

public import Balaban.LargeField.R.WindowCollarGeom
public import Balaban.LargeField.R.DeltaPsiDef
public import Balaban.LargeField.R.DeltaPhi
import Mathlib.Tactic.Linarith

/-!
# The inherited physical datum and the corrected `δψ′` (COLLAR-FIX §§1, 2)

The physical datum of the window background is the trace of the inherited parent multiscale field
(COLLAR-FIX (1.1)-(1.2)):

* `inheritedField W ψ = psiTilde W.full ψ`: the parent lift of `ψ`;
* `parentLift_layerConst`: it is constant on the blocks of the window generating set `G`
  (`ParentRefines`), so `physicalWindowData` (= `BgData.clip G` of it) is typed;
* `physical_window_action_reads_inherited`: the window action (and the source) evaluated with this
  datum read exactly the spins `ψ(parentBlock B x)` of the parent on `dataSites G`: any datum with the
  same trace on `dataSites G` gives the same action;
* `deltaPsiColl`: the corrected `δψ′`, the difference of the two actual `BgData.Ψ` fields (physical datum and
  reference `windowData`) on *all* data sites `Ω₁ ∪ C`, zero beyond;
* `deltaPsiColl_eq_zero_outer`: the exact outer-collar identity (2.1), `δψ′ = 0` on `C_out`;
* comparison lemmas with the landed `psiTilde`, `psiTildeData`, `deltaPsi`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-! ### `ParentRefines` is inhabited -/

theorem parentRefines_self (G : GeneratingSet d L N₀ k ϱ) : ParentRefines G G :=
  parentRefines_of_subset G G fun _ _ _ _ hx => ((GeneratingSet.mem_layer _).1 hx).1

/-- `ParentRefines` for the window generating set is inhabited (for the sample pieces). -/
theorem exists_window_parentRefines :
    ∃ (W : WindowPieces d L N₀ k ϱ) (hWh : W.Hyp), ParentRefines (W.windowGenSet hWh) W.full :=
  ⟨WindowPieces.sample, WindowPieces.sample_hyp,
    window_parent_refines _ _ (fun n _ _ => by simp [WindowPieces.sample])
      (fun n _ _ => by simp [WindowPieces.sample])⟩

/-! ### The inherited field and the physical datum -/

section Inherited

variable (W : WindowPieces d L N₀ k ϱ)

/-- **`inheritedField W ψ`** (COLLAR-FIX (1.1)): the parent lift of the multiscale field `ψ`,
`x ↦ ψ(p_B(x))` with `B = W.full = 𝔹_k`, i.e. `psiTilde W.full ψ`. -/
noncomputable def inheritedField (ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N))
    (x : Torus d (N₀ * L ^ k)) : Fin N → ℝ :=
  psiTilde W.full ψ x

theorem inheritedField_eq_parentBlock (ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N))
    (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    inheritedField W ψ x i = ψ (parentBlock W.full x) i := by
  classical
  unfold inheritedField psiTilde parentBlock
  by_cases hx : x ∈ W.full.Ω 1 <;> simp [hx]

/-- **`parentLift_layerConst`**: the parent lift is constant on the blocks of every layer of the window
generating set, as soon as the parent refines it. -/
theorem parentLift_layerConst (hWh : W.Hyp)
    (href : ParentRefines (W.windowGenSet hWh) W.full)
    (ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) :
    IsLayerConstant (W.windowGenSet hWh) (fun x i => ((inheritedField W ψ x i : ℝ) : ℂ)) := by
  intro n hn1 hnk x hx x' hx'
  funext i
  simp only [inheritedField_eq_parentBlock, href n hn1 hnk x hx x' hx']

/-- **The physical datum** (COLLAR-FIX (1.1)-(1.2)): `BgData.clip G` of the parent lift (with the constant
`h`), on `dataSites G = Ω₁(G) ∪ C_G`.  Typed by `ParentRefines`. -/
noncomputable def physicalWindowData (hWh : W.Hyp)
    (href : ParentRefines (W.windowGenSet hWh) W.full)
    (ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ) :
    BgData (W.windowGenSet hWh) N :=
  BgData.clip (W.windowGenSet hWh) (fun x i => ((inheritedField W ψ x i : ℝ) : ℂ))
    (fun _ i => ((h i : ℝ) : ℂ)) (parentLift_layerConst W hWh href ψ) (fun _ _ _ _ _ _ _ => rfl)

variable (hWh : W.Hyp) (href : ParentRefines (W.windowGenSet hWh) W.full)
  (ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)

theorem physicalWindowData_Ψ {x : Torus d (N₀ * L ^ k)} (hx : x ∈ dataSites (W.windowGenSet hWh))
    (i : Fin N) :
    (physicalWindowData W hWh href ψ h).Ψ x i = ((inheritedField W ψ x i : ℝ) : ℂ) := by
  classical
  simp [physicalWindowData, BgData.clip, hx]

theorem physicalWindowData_Ψ_of_not_mem {x : Torus d (N₀ * L ^ k)}
    (hx : x ∉ dataSites (W.windowGenSet hWh)) (i : Fin N) :
    (physicalWindowData W hWh href ψ h).Ψ x i = 0 := by
  rw [(physicalWindowData W hWh href ψ h).Ψ_zero x hx]; rfl

theorem physicalWindowData_h {x : Torus d (N₀ * L ^ k)} (hx : x ∈ (W.windowGenSet hWh).Ω 1)
    (i : Fin N) : (physicalWindowData W hWh href ψ h).h x i = ((h i : ℝ) : ℂ) := by
  classical
  simp [physicalWindowData, BgData.clip, hx]

/-- **COLLAR-FIX (1.2)**: the Dirichlet collar of the physical datum is the parent lift. -/
theorem physicalWindowData_collar {c : Torus d (N₀ * L ^ k)}
    (hc : c ∈ collar (W.windowGenSet hWh)) (i : Fin N) :
    (physicalWindowData W hWh href ψ h).Ψ c i =
      if c ∈ W.full.Ω 1 then ((ψ (blockOf d L N₀ k (W.full.layerIndex c) c) i : ℝ) : ℂ)
      else ((ψ ⟨0, c⟩ i : ℝ) : ℂ) := by
  classical
  rw [physicalWindowData_Ψ W hWh href ψ h ((mem_dataSites _).2 (Or.inr hc))]
  unfold inheritedField psiTilde
  by_cases hx : c ∈ W.full.Ω 1 <;> simp [hx]

end Inherited

/-! ### Action and source read only the trace on the data sites -/

section ActionReads

variable (G : GeneratingSet d L N₀ k ϱ)

theorem barField_congr {Ψ Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (φ : G.Ω 1 × Fin N → ℂ)
    {y : Torus d (N₀ * L ^ k)} (hΨ : Ψ' y = Ψ y) (i : Fin N) :
    barField G Ψ' φ y i = barField G Ψ φ y i := by
  unfold barField
  by_cases h : y ∈ G.Ω 1
  · simp [h]
  · simp [h, congrFun hΨ i]

theorem mem_dataSites_of_bond {x : Torus d (N₀ * L ^ k)} {μ : Fin d}
    (hc : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1) :
    x ∈ dataSites G ∧ x + Pi.single μ 1 ∈ dataSites G := by
  by_cases hx : x ∈ G.Ω 1
  · refine ⟨(mem_dataSites G).2 (Or.inl hx), (mem_dataSites G).2 ?_⟩
    by_cases hy : x + Pi.single μ 1 ∈ G.Ω 1
    · exact Or.inl hy
    · exact Or.inr (mem_collar_of_adj G hx hy ⟨μ, Or.inl rfl⟩)
  · have hy : x + Pi.single μ 1 ∈ G.Ω 1 := hc.resolve_left hx
    exact ⟨(mem_dataSites G).2 (Or.inr (mem_collar_of_adj G hy hx ⟨μ, Or.inr rfl⟩)),
      (mem_dataSites G).2 (Or.inl hy)⟩

/-- The source `S(Ψ, h̃)` depends on the datum only through `Ψ|_{Ω₁ ∪ C}` and `h̃|_{Ω₁}`. -/
theorem source_congr (a : ℕ → ℝ) (ν : ℝ) (D D' : BgData G N)
    (hΨ : ∀ x ∈ dataSites G, D'.Ψ x = D.Ψ x) (hh : ∀ x ∈ G.Ω 1, D'.h x = D.h x) :
    source G a ν D' = source G a ν D := by
  funext p
  have e1 : D'.Ψ (p.1 : Torus d (N₀ * L ^ k)) = D.Ψ (p.1 : Torus d (N₀ * L ^ k)) :=
    hΨ _ ((mem_dataSites G).2 (Or.inl p.1.2))
  have e2 : D'.h (p.1 : Torus d (N₀ * L ^ k)) = D.h (p.1 : Torus d (N₀ * L ^ k)) := hh _ p.1.2
  have key : ∀ y, (if y ∈ collar G then D'.Ψ y p.2 else 0) =
      (if y ∈ collar G then D.Ψ y p.2 else 0) := fun y => by
    by_cases hy : y ∈ collar G
    · simp [hy, hΨ y ((mem_dataSites G).2 (Or.inr hy))]
    · simp [hy]
  simp only [source, qStar, boundaryTerm, e1, e2, key]

/-- The action `A(φ)` depends on the datum only through `Ψ|_{Ω₁ ∪ C}` and `h̃|_{Ω₁}`. -/
theorem action_congr (a : ℕ → ℝ) (ν : ℝ) (D D' : BgData G N)
    (hΨ : ∀ x ∈ dataSites G, D'.Ψ x = D.Ψ x) (hh : ∀ x ∈ G.Ω 1, D'.h x = D.h x)
    (φ : G.Ω 1 × Fin N → ℂ) : action G a ν D' φ = action G a ν D φ := by
  have e1 : ∀ x : G.Ω 1, D'.Ψ (x : Torus d (N₀ * L ^ k)) = D.Ψ (x : Torus d (N₀ * L ^ k)) :=
    fun x => hΨ _ ((mem_dataSites G).2 (Or.inl x.2))
  have e3 : ∀ x : G.Ω 1, D'.h (x : Torus d (N₀ * L ^ k)) = D.h (x : Torus d (N₀ * L ^ k)) :=
    fun x => hh _ x.2
  have e2 : ∀ (x : Torus d (N₀ * L ^ k)) (μ : Fin d),
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, ‖barField G D'.Ψ φ (x + Pi.single μ 1) i - barField G D'.Ψ φ x i‖ ^ 2 else 0) =
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, ‖barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i‖ ^ 2 else 0) := by
    intro x μ
    split_ifs with hc
    · obtain ⟨h1, h2⟩ := mem_dataSites_of_bond G hc
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [barField_congr G φ (hΨ _ h2) i, barField_congr G φ (hΨ _ h1) i]
    · rfl
  unfold action
  simp only [e1, e3, e2]

end ActionReads

section Reads

variable (W : WindowPieces d L N₀ k ϱ) (hWh : W.Hyp) (href : ParentRefines (W.windowGenSet hWh) W.full)
  (ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)

/-- **`physical_window_action_reads_inherited`** (COLLAR-FIX §1, "the density is unchanged"): the
physical datum reads, on every data site `x ∈ Ω₁(G) ∪ C_G`, the spin `ψ(parentBlock B x)` of the inherited
parent field, with the constant `h` on `Ω₁`; and the window source and action evaluated with it equal
those evaluated with any datum having the same trace on the data sites. -/
theorem physical_window_action_reads_inherited :
    (∀ x ∈ dataSites (W.windowGenSet hWh), ∀ i,
      (physicalWindowData W hWh href ψ h).Ψ x i = ((ψ (parentBlock W.full x) i : ℝ) : ℂ)) ∧
    (∀ x ∈ (W.windowGenSet hWh).Ω 1, ∀ i,
      (physicalWindowData W hWh href ψ h).h x i = ((h i : ℝ) : ℂ)) ∧
    ∀ D' : BgData (W.windowGenSet hWh) N,
      (∀ x ∈ dataSites (W.windowGenSet hWh), ∀ i,
        D'.Ψ x i = ((ψ (parentBlock W.full x) i : ℝ) : ℂ)) →
      (∀ x ∈ (W.windowGenSet hWh).Ω 1, ∀ i, D'.h x i = ((h i : ℝ) : ℂ)) →
      ∀ (a : ℕ → ℝ) (ν : ℝ) (φ : (W.windowGenSet hWh).Ω 1 × Fin N → ℂ),
        action (W.windowGenSet hWh) a ν D' φ =
            action (W.windowGenSet hWh) a ν (physicalWindowData W hWh href ψ h) φ ∧
          source (W.windowGenSet hWh) a ν D' =
            source (W.windowGenSet hWh) a ν (physicalWindowData W hWh href ψ h) := by
  have hΨ : ∀ x ∈ dataSites (W.windowGenSet hWh), ∀ i,
      (physicalWindowData W hWh href ψ h).Ψ x i = ((ψ (parentBlock W.full x) i : ℝ) : ℂ) := by
    intro x hx i
    rw [physicalWindowData_Ψ W hWh href ψ h hx, inheritedField_eq_parentBlock]
  refine ⟨hΨ, fun x hx i => physicalWindowData_h W hWh href ψ h hx i, ?_⟩
  intro D' hD'Ψ hD'h a ν φ
  have c1 : ∀ x ∈ dataSites (W.windowGenSet hWh),
      D'.Ψ x = (physicalWindowData W hWh href ψ h).Ψ x := fun x hx =>
    funext fun i => by rw [hD'Ψ x hx i, hΨ x hx i]
  have c2 : ∀ x ∈ (W.windowGenSet hWh).Ω 1,
      D'.h x = (physicalWindowData W hWh href ψ h).h x := fun x hx =>
    funext fun i => by rw [hD'h x hx i, physicalWindowData_h W hWh href ψ h hx i]
  exact ⟨action_congr _ a ν _ _ c1 c2 φ, source_congr _ a ν _ _ c1 c2⟩

end Reads

/-! ### The corrected `δψ′` -/

section DeltaPsiColl

variable (W : WindowPieces d L N₀ k ϱ) (hWh : W.Hyp) (href : ParentRefines (W.windowGenSet hWh) W.full)
  (hprec : Precedes (W.windowGenSet hWh) W.bdry) (a : ℕ → ℝ)
  (ψ ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)

/-- **`δψ′`** (COLLAR-FIX §2): the difference of the two actual `BgData.Ψ` fields, the physical
datum (parent lift) and the reference `windowData` (the composed field `ψ⁰_{k₁,k}`), on *all* data sites
`Ω₁(G) ∪ C_G`; zero beyond them (both fields vanish there). -/
noncomputable def deltaPsiColl (x : Torus d (N₀ * L ^ k)) : Fin N → ℂ :=
  fun i => (physicalWindowData W hWh href ψ h).Ψ x i -
    (windowData (W.windowGenSet hWh) W.bdry hprec a ψ0 h).Ψ x i

theorem deltaPsiColl_of_mem {x : Torus d (N₀ * L ^ k)} (hx : x ∈ dataSites (W.windowGenSet hWh))
    (i : Fin N) :
    deltaPsiColl W hWh href hprec a ψ ψ0 h x i =
      ((psiTilde W.full ψ x i : ℝ) : ℂ) - psiZeroWin (W.windowGenSet hWh) W.bdry a ψ0 h x i := by
  classical
  unfold deltaPsiColl
  rw [physicalWindowData_Ψ W hWh href ψ h hx]
  simp [windowData, BgData.clip, hx, inheritedField]

theorem deltaPsiColl_of_not_mem {x : Torus d (N₀ * L ^ k)}
    (hx : x ∉ dataSites (W.windowGenSet hWh)) (i : Fin N) :
    deltaPsiColl W hWh href hprec a ψ ψ0 h x i = 0 := by
  classical
  unfold deltaPsiColl
  rw [physicalWindowData_Ψ_of_not_mem W hWh href ψ h hx]
  simp [windowData, BgData.clip, hx]

/-- On `Ω₁(G)`, `δψ′` is the landed `δψ` as soon as the parent layer of `x` is the layer of `x` in
`G`.  (In general it is not: on the lower core layers `n_G(x) < n_B(x)` the landed `ψ̃` reads
the child layer `ψ_{n_G}`, the parent lift reads `ψ_{n_B}`.) -/
theorem deltaPsiColl_eq_deltaPsi {x : Torus d (N₀ * L ^ k)} (hx : x ∈ (W.windowGenSet hWh).Ω 1)
    (hlay : W.full.layerIndex x = (W.windowGenSet hWh).layerIndex x) (i : Fin N) :
    deltaPsiColl W hWh href hprec a ψ ψ0 h x i =
      deltaPsi (W.windowGenSet hWh) W.bdry a ψ ψ0 h x i := by
  have hxd : x ∈ dataSites (W.windowGenSet hWh) := (mem_dataSites _).2 (Or.inl hx)
  have hxB : x ∈ W.full.Ω 1 := by
    by_contra hn
    have := layerIndex_of_not_mem W.full hn
    have h1 := ((W.windowGenSet hWh).layerIndex_spec hx).1
    omega
  rw [deltaPsiColl_of_mem W hWh href hprec a ψ ψ0 h hxd, deltaPsi_of_mem _ _ _ _ _ _ hx,
    psiTilde_of_mem _ ψ hxB, psiTilde_of_mem _ ψ hx, hlay]

/-- The layer indices of `G` and the parent agree on `Z ∖ Z_{k₁}` (the full piece). -/
theorem layerIndex_window_eq_full {x : Torus d (N₀ * L ^ k)} (hxZ : x ∈ W.Z) (hxc : x ∉ W.Zk1)
    (hx : x ∈ (W.windowGenSet hWh).Ω 1) :
    W.full.layerIndex x = (W.windowGenSet hWh).layerIndex x := by
  obtain ⟨h1, h2, hl⟩ := (W.windowGenSet hWh).layerIndex_spec hx
  have := (windowGen_mem_layer_iff W hWh hxZ hxc _).1 hl
  exact W.full.layerIndex_eq h1 h2 this

/-- On the outer piece `Z ∖ Z_{k₁}`, `δψ′ = δψ`. -/
theorem deltaPsiColl_eq_deltaPsi_outer {x : Torus d (N₀ * L ^ k)} (hx : x ∈ (W.windowGenSet hWh).Ω 1)
    (hxZ : x ∈ W.Z) (hxc : x ∉ W.Zk1) (i : Fin N) :
    deltaPsiColl W hWh href hprec a ψ ψ0 h x i =
      deltaPsi (W.windowGenSet hWh) W.bdry a ψ ψ0 h x i :=
  deltaPsiColl_eq_deltaPsi W hWh href hprec a ψ ψ0 h hx (layerIndex_window_eq_full W hWh hxZ hxc hx) i

/-- The landed collar value `ψ̃ - ψ⁰` (the child `psiTilde G`, layer `0` on the collar) and the
corrected one differ on `C_G` exactly by the parent lift minus the fine-scale spin. -/
theorem deltaPsiColl_collar_sub {c : Torus d (N₀ * L ^ k)} (hc : c ∈ collar (W.windowGenSet hWh))
    (i : Fin N) :
    deltaPsiColl W hWh href hprec a ψ ψ0 h c i -
        (((psiTilde (W.windowGenSet hWh) ψ c i : ℝ) : ℂ) -
          psiZeroWin (W.windowGenSet hWh) W.bdry a ψ0 h c i) =
      ((psiTilde W.full ψ c i : ℝ) : ℂ) - ((ψ ⟨0, c⟩ i : ℝ) : ℂ) := by
  have hcG : c ∉ (W.windowGenSet hWh).Ω 1 := ((mem_collar _).1 hc).1
  rw [deltaPsiColl_of_mem W hWh href hprec a ψ ψ0 h ((mem_dataSites _).2 (Or.inr hc))]
  have : psiTilde (W.windowGenSet hWh) ψ c i = ψ ⟨0, c⟩ i := by simp [psiTilde, hcG]
  rw [this]; ring

/-- Off `Ω₁(B)` the corrected and the landed collar values agree. -/
theorem deltaPsiColl_collar_eq_of_not_mem {c : Torus d (N₀ * L ^ k)}
    (hc : c ∈ collar (W.windowGenSet hWh)) (hcB : c ∉ W.full.Ω 1) (i : Fin N) :
    deltaPsiColl W hWh href hprec a ψ ψ0 h c i =
      ((psiTilde (W.windowGenSet hWh) ψ c i : ℝ) : ℂ) -
        psiZeroWin (W.windowGenSet hWh) W.bdry a ψ0 h c i := by
  have hcG : c ∉ (W.windowGenSet hWh).Ω 1 := ((mem_collar _).1 hc).1
  rw [deltaPsiColl_of_mem W hWh href hprec a ψ ψ0 h ((mem_dataSites _).2 (Or.inr hc))]
  simp [psiTilde, hcG, hcB]

/-- The physical datum is the landed `psiTildeData G ψ h` wherever the parent lift and the child `ψ̃` agree on
the data sites (in particular when the layers agree on `Ω₁(G)` and the collar is off `Ω₁(B)`). -/
theorem physicalWindowData_eq_psiTildeData
    (hagree : ∀ x ∈ dataSites (W.windowGenSet hWh),
      psiTilde W.full ψ x = psiTilde (W.windowGenSet hWh) ψ x) :
    physicalWindowData W hWh href ψ h = psiTildeData (W.windowGenSet hWh) ψ h := by
  classical
  unfold physicalWindowData psiTildeData BgData.clip inheritedField
  congr 1
  funext x
  by_cases hx : x ∈ dataSites (W.windowGenSet hWh)
  · simp [hx, hagree x hx]
  · simp [hx]

/-- **COLLAR-FIX (2.1), the exact outer-collar identity**: `δψ′ = 0` on `C_out = C_G ∖ Z_{k₁}`.
Premises (not fields of `WindowPieces.Hyp`): Lemma III.1.2 (f) in the form `Ω_{k₁}(B)ᶜ ⊆ Z_{k₁}`
(`hOmK1`) and `Ω_k(B)ᶜ ⊆ Z` (`hOmK`); the support `Ω₁(𝔹_k(U_k)) ⊆ U^∼_k` (`hsupp`); `𝔹_{k₁,k} ≺ 𝔹_k(U_k)`
(`hprec`, typing of `windowData`); and P7 (2.44) `ψ⁰_k = ψ_k` off `Z` on the data sites of `𝔹_k(U_k)`
(`hoff`). -/
theorem deltaPsiColl_eq_zero_outer (hk : 1 ≤ k)
    (hOmK1 : ∀ x, x ∉ W.Zk1 → x ∈ W.full.Ω 1) (hsupp : ∀ x ∈ W.bdry.Ω 1, x ∈ W.Unb)
    (hOmK : ∀ x, x ∉ W.Z → x ∈ W.full.Ω k)
    (hoff : ∀ x ∈ dataSites W.bdry, x ∉ W.Z →
      ψ0 ⟨k, jBlock d L N₀ k k x⟩ = ψ ⟨k, jBlock d L N₀ k k x⟩)
    {c : Torus d (N₀ * L ^ k)} (hc : c ∈ collarOut W hWh) (i : Fin N) :
    deltaPsiColl W hWh href hprec a ψ ψ0 h c i = 0 := by
  classical
  obtain ⟨hcol, -⟩ := (mem_collarOut W hWh).1 hc
  obtain ⟨hcZ, hcb⟩ := outer_collar_outside_reference W hWh hOmK1 hsupp hc
  obtain ⟨-, hli, -⟩ := outer_collar_parent_layer_top W hWh hk hOmK1 hsupp hOmK hc
  have hcd : c ∈ dataSites (W.windowGenSet hWh) := (mem_dataSites _).2 (Or.inr hcol)
  have hcB : c ∈ W.full.Ω 1 := W.full.layer_subset hk le_rfl
    ((GeneratingSet.mem_layer _).2 ⟨hOmK c hcZ, by simp [W.full.top]⟩)
  -- `c` is in the collar of `𝔹_k(U_k)`
  obtain ⟨-, x, hx, hadj⟩ := (mem_collar _).1 hcol
  have hcol' : c ∈ collar W.bdry := (mem_collar _).2 ⟨hcb, x, hprec.mem_Ω1 hx, hadj⟩
  have hcd' : c ∈ dataSites W.bdry := (mem_dataSites _).2 (Or.inr hcol')
  rw [deltaPsiColl_of_mem W hWh href hprec a ψ ψ0 h hcd]
  have e1 : psiTilde W.full ψ c i = ψ ⟨k, jBlock d L N₀ k k c⟩ i := by
    rw [psiTilde_of_mem _ ψ hcB, hli]; rfl
  have e2 : psiZeroWin (W.windowGenSet hWh) W.bdry a ψ0 h c i =
      ((ψ0 ⟨k, jBlock d L N₀ k k c⟩ i : ℝ) : ℂ) := by
    unfold psiZeroWin
    rw [composeField_of_collar a _ _ hcol i]
    unfold barField
    simp only [hcb, dite_false]
    unfold psiZeroData
    rw [liftSingle_Ψ W.bdry _ _ hcd']
  rw [e2, e1, hoff c hcd' hcZ]
  simp

end DeltaPsiColl

end Balaban.LargeField
