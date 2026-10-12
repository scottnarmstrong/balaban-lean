module

public import Balaban.LargeField.Base.BaseRecord
public import Balaban.LargeField.Base.BaseHistory
public import Balaban.LargeField.Base.SpinsNearBackground
public import Balaban.LargeField.Operators.HistGen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `BaseSpinSupport` from the base record (LF-RECONSTRUCTION Lemma II.7.5, first step)

The proof of Lemma II.7.5 starts: "By Lemma II.7.2 (d) every cube within distance `3` of `Ω₁` is
outside `P₁`, so `A = B = 1` there."  `baseSpinSupport_of_baseRecord` is this step: on the support
of the base decomposition term `χ'^{(0)c}(P₁) χ'^{(0)}(P₁^c)` (that is, `χ'^{(0)}(□') = 1` for
every cube `□' ∉ P₁`), the support data `BaseSpinSupport` of `spins_near_background` hold, for
the lifted data `D = lift_{0,1}(φ, θ)` of the generating set whose `Ω₁` is the fine set of `Ω₁`.
`RegionHistory.baseSpinSupport` is the same for the generating set `histGen` of a region history.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Finset

variable {d N L M : ℕ} {nn : ℕ → ℕ} [∀ k, NeZero (nn k)] [NeZero M] [NeZero L] {ϱ : ℝ}

/-- The block average of `spinAverage` is the one of `spinBlockAverage` at `K = 1`. -/
theorem spinAverage_eq_spinBlockAverage (G : GeneratingSet d L (M * nn 1) 1 ϱ)
    (φ : Torus d (M * nn 1 * L ^ 1) → Fin N → ℝ) (x : Torus d (M * nn 1 * L ^ 1)) (i : Fin N) :
    spinAverage nn L M 1 φ (jBlock d L (M * nn 1) 1 1 x) i = spinBlockAverage G φ x i := by
  classical
  unfold spinAverage spinBlockAverage
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext z
  rw [Finset.mem_filter, GeneratingSet.mem_blk]
  simp only [Finset.mem_univ, true_and]
  unfold jBlock
  exact iff_of_eq (by
    have e : ∀ w : Torus d (M * nn 1 * L ^ 1), blockMap (L ^ 1) (M * nn 1 * L ^ (1 - 1)) w =
        blockMap L (M * nn 1 * L ^ (1 - 1)) w := fun w =>
      congrArg (fun K => blockMap K (M * nn 1 * L ^ (1 - 1)) w) (pow_one L)
    rw [e z, e x])

/-- A site of `Ω₁ ∪ C(Ω₁)` lies in a cube at index distance `≤ 1` from `Ω₁`. -/
theorem exists_near_of_mem_dataSites (hnn : ∀ i, i < 1 → nn i = L * nn (i + 1)) {Rk : ℝ}
    (G : GeneratingSet d L (M * nn 1) 1 ϱ) (br : BaseRecord d L (nn 1) Rk)
    (hΩ : ∀ x, x ∈ G.Ω 1 ↔ cubeMap nn L M 1 1 x ∈ br.Omega)
    {x : Torus d (M * nn 1 * L ^ 1)} (hx : x ∈ dataSites G) :
    ∃ o ∈ br.Omega, supDist (cubeMap nn L M 1 1 x) o ≤ 3 := by
  rcases (mem_dataSites G).1 hx with h | h
  · exact ⟨_, (hΩ x).1 h, by rw [supDist_self]; omega⟩
  · obtain ⟨-, x₀, hx₀, μ, hμ | hμ⟩ := (mem_collar G).1 h
    · refine ⟨cubeMap nn L M 1 1 x₀, (hΩ x₀).1 hx₀, ?_⟩
      have := supDist_cubeMap_add_single_le (M := M) (L := L) (K := 1) hnn le_rfl x₀ μ
      rw [supDist_comm, hμ]; omega
    · refine ⟨cubeMap nn L M 1 1 x₀, (hΩ x₀).1 hx₀, ?_⟩
      have := supDist_cubeMap_add_single_le (M := M) (L := L) (K := 1) hnn le_rfl x μ
      rw [hμ]; omega

open Classical in
/-- **Lemma II.7.5, first step (`BaseSpinSupport` from the base record).**  Let `br` be a base
record and `G` a generating set (`K = 1`) whose `Ω₁` is the fine set of the `Ω₁` of `br`.  Let
`φ` be a spin field (`|φ_x| = 1`), `h` a unit vector, `θ` a block field, and `D` the lifted data
`lift_{0,1}(φ, θ)`: `Ψ = θ` on the blocks of `Ω₁`, `Ψ = φ` on the collar, `h̃ = h` on `Ω₁`.  If
`χ'^{(0)}(□') = 1` for every cube `□' ∉ P₁` (the support of the base decomposition summand of
`br`), then `BaseSpinSupport` holds for `D` (with `ν` the site coefficient in regime (B) and `0`
in regime (A)). -/
theorem baseSpinSupport_of_baseRecord (hnn : ∀ i, i < 1 → nn i = L * nn (i + 1)) {Rk : ℝ}
    (G : GeneratingSet d L (M * nn 1) 1 ϱ) (br : BaseRecord d L (nn 1) Rk)
    (hΩ : ∀ x, x ∈ G.Ω 1 ↔ cubeMap nn L M 1 1 x ∈ br.Omega)
    (regimeB : Prop) (ν δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (φ : Torus d (M * nn 1 * L ^ 1) → Fin N → ℝ)
    (θ : Torus d (M * nn 1 * L ^ (1 - 1)) → Fin N → ℝ) (h : Fin N → ℝ)
    (hφ : ∀ x, ∑ i, φ x i ^ 2 = 1) (hh : ∑ i, h i ^ 2 = 1) (D : BgData G N)
    (hDΨ : ∀ x ∈ G.Ω 1, ∀ i, D.Ψ x i = (θ (jBlock d L (M * nn 1) 1 1 x) i : ℂ))
    (hDc : ∀ x ∈ collar G, ∀ i, D.Ψ x i = (φ x i : ℂ))
    (hDh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (h i : ℂ))
    (hsupp : ∀ c : Torus d (nn 1), c ∉ br.P →
      chiPrimeZero nn L M 1 regimeB ν δ₀ h c (φ, θ) = 1) :
    BaseSpinSupport G (if regimeB then ν else 0) δ₀ φ h D := by
  have hcube : ∀ x ∈ dataSites G, cubeMap nn L M 1 1 x ∉ br.P := fun x hx =>
    br.not_mem_P_of_near_Omega (exists_near_of_mem_dataSites hnn G br hΩ hx)
  have hunpack : ∀ x ∈ dataSites G,
      ChiBlockProp nn L M 1 δ₀ φ θ (cubeMap nn L M 1 1 x) ∧
        ChiBondProp nn L M 1 δ₀ φ (cubeMap nn L M 1 1 x) ∧
        (regimeB → ChiSiteProp nn L M 1 ν δ₀ φ h (cubeMap nn L M 1 1 x)) := fun x hx =>
    (chiPrimeZero_eq_one_iff nn L M 1 regimeB ν δ₀ h _ (φ, θ)).1 (hsupp _ (hcube x hx))
  refine
    { delta_pos := hδ₀
      spin_unit := hφ
      h_unit := hh
      block_real := fun x hx i => by rw [hDΨ x hx i]; simp
      collar_eq := hDc
      field_eq := hDh
      block_cond := ?_
      bond_cond := ?_
      site_cond := ?_ }
  · intro x hx
    have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    have hb := (hunpack x hxd).1 (jBlock d L (M * nn 1) 1 1 x)
      (cubeMap_eq_comp hnn le_rfl x)
    have e : (fun i => (D.Ψ x i).re - spinBlockAverage G φ x i) =
        fun i => θ (jBlock d L (M * nn 1) 1 1 x) i -
          spinAverage nn L M 1 φ (jBlock d L (M * nn 1) 1 1 x) i := by
      funext i
      rw [hDΨ x hx i, spinAverage_eq_spinBlockAverage G]
      simp
    rw [e]; exact hb
  · intro x μ hx
    rcases hx with hx | hx
    · exact (hunpack x hx).2.1 x μ (Or.inl rfl)
    · exact (hunpack _ hx).2.1 x μ (Or.inr rfl)
  · intro x hx
    split_ifs with hB
    · exact (hunpack x hx).2.2 hB x rfl
    · simpa using pow_pos hδ₀ 2

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) {M : ℕ} [NeZero M] [NeZero S.L]

theorem mem_histGen_one_iff (hK1 : 1 ≤ K) (hrem : ∀ k, H.rem k = ∅) (hL : 2 ≤ S.L)
    (x : Torus S.d (M * n 1 * S.L ^ 1)) :
    x ∈ (H.histGen (M := M) (K' := 1) hK1 hrem hL (fun j h1 h2 => by omega)).Ω 1 ↔
      cubeMap n S.L M 1 1 x ∈ H.baseRecord.Omega := by
  rw [H.mem_histGen (K' := 1) hK1 hrem hL _ 1 x]
  have h := baseRecord_isStep H.baseRecord (n 0) (R (0 - 1))
  rw [H.baseRecord_toStep] at h
  rw [← h.2.2.2.2.2.2.2.2.1]
  simp only [RegionSeq.OmegaAt_succ]
  exact and_iff_right le_rfl

open Classical in
/-- **Lemma II.7.5, first step** for the generating set of a region history (without removals):
`BaseSpinSupport` follows from the base record `H.baseRecord` and the support of the base
decomposition term (`χ'^{(0)}(□') = 1` for the cubes `□' ∉ P₁`). -/
theorem baseSpinSupport (hK1 : 1 ≤ K) (hrem : ∀ k, H.rem k = ∅) (hL : 2 ≤ S.L)
    (regimeB : Prop) (ν δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    {N : ℕ} (φ : Torus S.d (M * n 1 * S.L ^ 1) → Fin N → ℝ)
    (θ : Torus S.d (M * n 1 * S.L ^ (1 - 1)) → Fin N → ℝ) (h : Fin N → ℝ)
    (hφ : ∀ x, ∑ i, φ x i ^ 2 = 1) (hh : ∑ i, h i ^ 2 = 1)
    (D : BgData (H.histGen (M := M) (K' := 1) hK1 hrem hL (fun j h1 h2 => by omega)) N)
    (hDΨ : ∀ x ∈ (H.histGen (M := M) (K' := 1) hK1 hrem hL (fun j h1 h2 => by omega)).Ω 1, ∀ i,
      D.Ψ x i = (θ (jBlock S.d S.L (M * n 1) 1 1 x) i : ℂ))
    (hDc : ∀ x ∈ collar (H.histGen (M := M) (K' := 1) hK1 hrem hL (fun j h1 h2 => by omega)), ∀ i,
      D.Ψ x i = (φ x i : ℂ))
    (hDh : ∀ x ∈ (H.histGen (M := M) (K' := 1) hK1 hrem hL (fun j h1 h2 => by omega)).Ω 1, ∀ i,
      D.h x i = (h i : ℂ))
    (hsupp : ∀ c : Torus S.d (n 1), c ∉ H.baseRecord.P →
      chiPrimeZero n S.L M 1 regimeB ν δ₀ h c (φ, θ) = 1) :
    BaseSpinSupport (H.histGen (M := M) (K' := 1) hK1 hrem hL (fun j h1 h2 => by omega))
      (if regimeB then ν else 0) δ₀ φ h D :=
  baseSpinSupport_of_baseRecord (fun i hi => H.F.hnn i (by omega)) _ H.baseRecord
    (H.mem_histGen_one_iff hK1 hrem hL)
    regimeB ν δ₀ hδ₀ φ θ h hφ hh D hDΨ hDc hDh hsupp

end RegionHistory

end Balaban.LargeField
