module

public import Balaban.LargeField.Characteristic.Reg
public import Balaban.SmallField.XiLatSymm

/-!
# Lattice-symmetry covariance of the regularity predicate

For a lattice symmetry `S : LatSymm G G' σ` (`Balaban/Background/EquivarianceLat.lean`) and the
transported datum `S.sym D`, the predicate `Reg` of Definition II.3.1 (and `RegC`, `RegIneq`,
`RegMixedIneq`) at the transported data and the transported sets `T.map σ` is equivalent to the
predicate at `D` and `T`.  The ingredients: the block averages (`blockAvg_sym_all`, including
the collar sites), the extension `φ̄` and its Laplacian (`barVec_sym`, `barLap_sym`), the
orientation-reversing and direction-permuting steps (`NbrSymm`), the background (`bgFieldC_sym`),
and the data domains (`inUnionDomainR_sym_iff`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

set_option linter.unusedSectionVars false

section RegSymm

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G G' : GeneratingSet d L N₀ q ϱ} {σ : Equiv.Perm (Torus d (N₀ * L ^ q))}
  (S : LatSymm G G' σ)

include S

theorem _root_.Balaban.Background.LatSymm.blockAvg_sym_all (φ : G.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ q)) (i : Fin N) :
    blockAvg G' (S.fld φ) (σ x) i = blockAvg G φ x i := by
  by_cases hx : x ∈ G.Ω 1
  · exact S.blockAvg_sym φ hx i
  · have hx' : σ x ∉ G'.Ω 1 := fun h => hx ((S.mem_Ω1 x).1 h)
    have hz : ∀ (H : GeneratingSet d L N₀ q ϱ) (ψ : H.Ω 1 × Fin N → ℂ) (y : Torus d (N₀ * L ^ q)),
        y ∉ H.Ω 1 → blockAvg H ψ y i = 0 := by
      intro H ψ y hy
      unfold blockAvg
      rw [layerIndex_of_not_mem H hy]
      have : H.blk 0 y = {y} := by
        ext z
        rw [GeneratingSet.mem_blk, Finset.mem_singleton]
        constructor
        · intro h
          funext i
          have := congrFun h i
          simpa [jBlock, blockMap, blockCoord] using this
        · rintro rfl; rfl
      rw [this, Finset.sum_singleton, svec_of_not_mem H ψ hy]
      simp
    rw [hz G φ x hx, hz G' _ _ hx']


theorem _root_.Balaban.Background.LatSymm.barVec_sym (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ q)) :
    barVec G' (S.sym D) (S.fld φ) (σ x) = barVec G D φ x :=
  funext fun i => S.barField_sym D φ x i

theorem _root_.Balaban.Background.LatSymm.blockDev_sym (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ q)) :
    blockDev G' (S.sym D) (S.fld φ) (σ x) = blockDev G D φ x := by
  unfold blockDev
  congr 1
  funext i
  rw [S.blockAvg_sym_all φ x i]
  simp [Balaban.Background.LatSymm.sym]

theorem _root_.Balaban.Background.LatSymm.blockClose_sym (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ)
    (T : Finset (Torus d (N₀ * L ^ q))) (δ : ℝ) :
    BlockClose G' (S.sym D) (S.fld φ) (T.map σ.toEmbedding) δ ↔ BlockClose G D φ T δ := by
  unfold BlockClose
  simp only [Finset.mem_map_equiv]
  constructor
  · intro h x hx
    have := h (σ x) (by simpa using hx)
    rwa [S.blockDev_sym] at this
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ : ∃ y, y ∈ T ∧ σ y = x := ⟨σ.symm x, by simpa using hx, by simp⟩
    rw [S.blockDev_sym]
    exact h y hy

theorem _root_.Balaban.Background.LatSymm.barLap_sym (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ q)) :
    barLap G' (S.sym D) (S.fld φ) (σ x) = barLap G D φ x := by
  unfold barLap
  rw [← Equiv.sum_comp S.perm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h := S.bdry_swap (fun z => barVec G' (S.sym D) (S.fld φ) z) x μ
  simp only [S.barVec_sym] at h
  rw [h, S.barVec_sym]


theorem _root_.Balaban.Background.LatSymm.conj_swap (P : Torus d (N₀ * L ^ q) → Prop)
    (x : Torus d (N₀ * L ^ q)) (μ : Fin d) :
    (P (σ x + Pi.single (S.perm μ) 1) ∧ P (σ x - Pi.single (S.perm μ) 1)) ↔
      (P (σ (x + Pi.single μ 1)) ∧ P (σ (x - Pi.single μ 1))) := by
  rw [S.step, S.step_sub]
  cases S.flip μ
  · simp
  · simp [and_comm]

theorem _root_.Balaban.Background.LatSymm.gradClose_sym (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) (ℓ : ℝ) (T : Finset (Torus d (N₀ * L ^ q))) (δ : ℝ) :
    GradClose G' (S.sym D) (S.fld φ) (S.mul α) ℓ (T.map σ.toEmbedding) δ ↔
      GradClose G D φ α ℓ T δ := by
  unfold GradClose
  have key : ∀ x : G.Ω 1,
      ((∀ μ : Fin d, ℓ * vn (barVec G' (S.sym D) (S.fld φ) ((S.Ω1Equiv x : Torus d (N₀ * L ^ q)) +
          Pi.single μ 1) - barVec G' (S.sym D) (S.fld φ) (S.Ω1Equiv x : Torus d (N₀ * L ^ q))) < δ ∧
        ℓ * vn (barVec G' (S.sym D) (S.fld φ) ((S.Ω1Equiv x : Torus d (N₀ * L ^ q)) - Pi.single μ 1) -
          barVec G' (S.sym D) (S.fld φ) (S.Ω1Equiv x : Torus d (N₀ * L ^ q))) < δ) ∧
        ℓ ^ 2 * vn (barLap G' (S.sym D) (S.fld φ) (S.Ω1Equiv x : Torus d (N₀ * L ^ q))) < δ ∧
        ℓ ^ 2 * ‖S.mul α (S.Ω1Equiv x)‖ < δ) ↔
      ((∀ μ : Fin d, ℓ * vn (barVec G D φ ((x : Torus d (N₀ * L ^ q)) + Pi.single μ 1) -
          barVec G D φ x) < δ ∧
        ℓ * vn (barVec G D φ ((x : Torus d (N₀ * L ^ q)) - Pi.single μ 1) - barVec G D φ x) < δ) ∧
        ℓ ^ 2 * vn (barLap G D φ x) < δ ∧ ℓ ^ 2 * ‖α x‖ < δ) := by
    intro x
    rw [S.mul_apply, S.coe_Ω1Equiv, S.barLap_sym]
    simp only [S.barVec_sym]
    refine and_congr ?_ Iff.rfl
    constructor
    · intro h μ
      have := h (S.perm μ)
      have e := S.conj_swap (fun z => ℓ * vn (barVec G' (S.sym D) (S.fld φ) z -
        barVec G D φ x) < δ) (x : Torus d (N₀ * L ^ q)) μ
      simp only [S.barVec_sym] at e
      exact e.mp this
    · intro h μ'
      obtain ⟨μ, rfl⟩ := S.perm.surjective μ'
      have e := S.conj_swap (fun z => ℓ * vn (barVec G' (S.sym D) (S.fld φ) z -
        barVec G D φ x) < δ) (x : Torus d (N₀ * L ^ q)) μ
      simp only [S.barVec_sym] at e
      exact e.mpr (h μ)
  constructor
  · intro h x hx
    exact (key x).mp (h (S.Ω1Equiv x) (by simpa using hx))
  · intro h x' hx'
    obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective x'
    refine (key x).mpr (h x ?_)
    simpa using hx'


theorem _root_.Balaban.Background.LatSymm.symm_sym (D : BgData G N) :
    S.symm.sym (S.sym D) = D := by
  refine Balaban.Background.BgData.ext' (funext fun y => ?_) (funext fun y => ?_) <;>
    simp [Balaban.Background.LatSymm.sym]

theorem _root_.Balaban.Background.LatSymm.inUnionDomainR_sym_iff {c₁ ν : ℝ} (D : BgData G N) :
    InUnionDomainR G' c₁ ν (S.sym D) ↔ InUnionDomainR G c₁ ν D := by
  refine ⟨fun H => ?_, Balaban.SmallField.inUnionDomainR_sym S⟩
  have := Balaban.SmallField.inUnionDomainR_sym S.symm H
  rwa [S.symm_sym] at this

theorem _root_.Balaban.Background.LatSymm.fieldClose_sym (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) (ν : ℝ) (T : Finset (Torus d (N₀ * L ^ q))) (δ : ℝ) :
    FieldClose G' (S.sym D) (S.fld φ) ν (T.map σ.toEmbedding) δ ↔ FieldClose G D φ ν T δ := by
  unfold FieldClose
  refine imp_congr_right fun _ => ?_
  constructor
  · intro h x hx
    have := h (S.Ω1Equiv x) (by simpa using hx)
    simpa [Balaban.Background.LatSymm.sym] using this
  · intro h x' hx'
    obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective x'
    have := h x (by simpa using hx')
    simpa [Balaban.Background.LatSymm.sym] using this

theorem _root_.Balaban.Background.LatSymm.regIneq_sym (a : ℕ → ℝ) (μ : ℝ) (D : BgData G N)
    (δ : ℝ) (T Tset : Finset (Torus d (N₀ * L ^ q))) :
    RegIneq G' a μ (S.sym D) δ (T.map σ.toEmbedding) (Tset.map σ.toEmbedding) ↔
      RegIneq G a μ D δ T Tset := by
  unfold RegIneq
  rw [(S.bgFieldC_sym a μ (bgC0 d L N) D).1, (S.bgFieldC_sym a μ (bgC0 d L N) D).2,
    S.blockClose_sym, S.gradClose_sym, S.fieldClose_sym]

theorem _root_.Balaban.Background.LatSymm.reg_sym_iff (a : ℕ → ℝ) (μ : ℝ) (D : BgData G N)
    (δ : ℝ) (T Tset : Finset (Torus d (N₀ * L ^ q))) :
    Reg G' a μ (S.sym D) δ (T.map σ.toEmbedding) (Tset.map σ.toEmbedding) ↔
      Reg G a μ D δ T Tset := by
  unfold Reg
  rw [S.inUnionDomainR_sym_iff, S.regIneq_sym]

theorem _root_.Balaban.Background.LatSymm.regMixedIneq_sym (a : ℕ → ℝ) (μ : ℝ) (D : BgData G N)
    (ℓ νk δ : ℝ) (Tfar Tnear Tset : Finset (Torus d (N₀ * L ^ q))) :
    RegMixedIneq G' a μ (S.sym D) ℓ νk δ (Tfar.map σ.toEmbedding) (Tnear.map σ.toEmbedding)
        (Tset.map σ.toEmbedding) ↔
      RegMixedIneq G a μ D ℓ νk δ Tfar Tnear Tset := by
  unfold RegMixedIneq
  rw [(S.bgFieldC_sym a μ (bgC0 d L N) D).1, (S.bgFieldC_sym a μ (bgC0 d L N) D).2,
    S.blockClose_sym, S.blockClose_sym, S.gradClose_sym, S.fieldClose_sym]


theorem _root_.Balaban.Background.LatSymm.inUnionDomainC_sym_iff {c₀ c₁ ν : ℝ} (D : BgData G N) :
    InUnionDomainC G' c₀ c₁ ν (S.sym D) ↔ InUnionDomainC G c₀ c₁ ν D := by
  refine ⟨fun H => ?_, Balaban.SmallField.inUnionDomainC_sym S⟩
  have := Balaban.SmallField.inUnionDomainC_sym S.symm H
  rwa [S.symm_sym] at this

theorem _root_.Balaban.Background.LatSymm.regC_sym_iff (a : ℕ → ℝ) (μ : ℝ) (D : BgData G N)
    (δ : ℝ) (T Tset : Finset (Torus d (N₀ * L ^ q))) :
    RegC G' a μ (S.sym D) δ (T.map σ.toEmbedding) (Tset.map σ.toEmbedding) ↔
      RegC G a μ D δ T Tset := by
  unfold RegC
  rw [S.inUnionDomainC_sym_iff, S.regIneq_sym]

end RegSymm
end Balaban.LargeField
