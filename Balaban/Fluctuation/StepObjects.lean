/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepMeasure
public import Balaban.Fluctuation.Lemma25Real
public import Balaban.Fluctuation.ExpansionReal
public import Balaban.SmallField.Def6
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The objects of one small-field RG step at `λ = ∞` (FLUCTUATION.md §2.1-§2.6)

Part A, the class composites on the step torus.  The class of Def-6 (`Ecomp`, `Fcomp`) is stated for
the torus index equal to the top level.  In the step `k → k+1` the old spin `ψ_k` is a field of level
`k` on the fine torus `CTorus d L N₁ m₁ (k+1)` (the torus on which the new level `k+1` lives, §1.1),
so the composites are re-stated for a top level `k ≤ K` on the torus of index `K`
(`composedDataAt`, `EcompAt`, `FcompAt`, `McompAt`); for `K = k` they are the composites of Def-6
(`EcompAt_top`, `FcompAt_top`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset

section ClassAt

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

theorem levelGS_precedes_at {j k : ℕ} (hj : j ≤ k) (hk : k ≤ K) :
    Precedes (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j (hj.trans hk))
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) := by
  intro i _ hik
  classical
  simp only [levelGS]
  split_ifs with h1 h2 <;>
    first | exact subset_rfl | exact Finset.empty_subset _ | (exfalso; omega)

/-- **The datum `ψ_k^{(j)}(ψ_k, h)`** (H.2) of the top datum `D` of level `k` on the torus of index
`K ≥ k`: `composeData` of the level-`j` set over the level-`k` set. -/
noncomputable def composedDataAt (a : ℕ → ℝ) (ν : ℝ) {j k : ℕ} (hj : j ≤ k) (hk : k ≤ K)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N) :
    BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j (hj.trans hk))
      N :=
  composeData (levelGS_precedes_at hj hk) a
    (bgField (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) a ν D) D

open Classical in
/-- The pair `(ψ_k^{(j)}, h)` of (H.2), `0` for `j > k`. -/
noncomputable def composedPairAt (a : ℕ → ℝ) (ν : ℝ) {k : ℕ} (hk : k ≤ K) (j : ℕ)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N) :
    Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N :=
  if hj : j ≤ k then ((composedDataAt a ν hj hk D).Ψ, (composedDataAt a ν hj hk D).h) else (0, 0)

/-- **`ℰ_k(ψ_k, h) = ∑_{j=1}^k ℰ^{(j)}(ψ_k^{(j)}(ψ_k, h), h)`** (H.2) for the top level `k ≤ K`. -/
noncomputable def EcompAt (m₀ : ℕ) (Tm : Terms d L N₁ m₁ K N ϱ) (a : ℕ → ℝ) (ν : ℝ) {k : ℕ}
    (hk : k ≤ K)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N) : ℂ :=
  ∑ j ∈ Finset.Icc 1 k, Edens m₀ Tm j (composedPairAt a ν hk j D).1 (composedPairAt a ν hk j D).2

/-- **The vector `ℳ_k(x; ψ_k, h, g)`** of (H.7) at the top level `k ≤ K`:
`φ_k(x) + ∑_{j=1}^k ℳ^{(j)}(x; ψ_k^{(j)}, h, g)`, so that `ℱ_k = ⟨g, ℳ_k⟩₁`. -/
noncomputable def McompAt (m₀ : ℕ) (Tm : Terms d L N₁ m₁ K N ϱ) (a : ℕ → ℝ) (ν : ℝ) {k : ℕ}
    (hk : k ≤ K)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N)
    (g : Fld d L N₁ m₁ K N) (x : CTorus d L N₁ m₁ K) : Fin N → ℂ := fun i =>
  svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
      (bgField (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) a ν D) x i +
    ∑ j ∈ Finset.Icc 1 k, Mloc m₀ Tm j x (composedPairAt a ν hk j D).1
      (composedPairAt a ν hk j D).2 g i

/-- **`ℱ_k(ψ_k, h, g) = ⟨g, φ_k⟩₁ + ∑_{j=1}^k ℱ^{(j)}(ψ_k^{(j)}, h, g)`** (H.7) for the top level
`k ≤ K`. -/
noncomputable def FcompAt (m₀ : ℕ) (Tm : Terms d L N₁ m₁ K N ϱ) (a : ℕ → ℝ) (ν : ℝ) {k : ℕ}
    (hk : k ≤ K)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N)
    (g : Fld d L N₁ m₁ K N) : ℂ :=
  (∑ x : CTorus d L N₁ m₁ K, ∑ i, g x i *
      svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
        (bgField (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) a ν D)
        x i) +
    ∑ j ∈ Finset.Icc 1 k, Floc m₀ Tm j (composedPairAt a ν hk j D).1
      (composedPairAt a ν hk j D).2 g

/-- For the top level equal to the torus index, `EcompAt` is the composite `Ecomp` of Def-6. -/
theorem EcompAt_top (m₀ : ℕ) (Tm : Terms d L N₁ m₁ K N ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (D : BgData (topGS d L N₁ m₁ K ϱ) N) :
    EcompAt m₀ Tm a ν (le_refl K) D = Ecomp m₀ Tm a ν D := rfl

/-- For the top level equal to the torus index, `FcompAt` is the composite `Fcomp` of Def-6. -/
theorem FcompAt_top (m₀ : ℕ) (Tm : Terms d L N₁ m₁ K N ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (D : BgData (topGS d L N₁ m₁ K ϱ) N) (g : Fld d L N₁ m₁ K N) :
    FcompAt m₀ Tm a ν (le_refl K) D g = Fcomp m₀ Tm a ν D g := rfl

/-- `ℱ_k = ⟨g, ℳ_k⟩₁`. -/
theorem FcompAt_eq_pair (m₀ : ℕ) (Tm : Terms d L N₁ m₁ K N ϱ) (a : ℕ → ℝ) (ν : ℝ) {k : ℕ}
    (hk : k ≤ K)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N)
    (g : Fld d L N₁ m₁ K N) :
    FcompAt m₀ Tm a ν hk D g = ∑ x : CTorus d L N₁ m₁ K, ∑ i, g x i * McompAt m₀ Tm a ν hk D g x i := by
  unfold FcompAt McompAt Floc
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

end ClassAt

section UnitLattice

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  {G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}

/-- **The lift of a field on the unit lattice `T^{(k)}_1`** (`unitPts G'`) to the fine torus: the
field that is constant on the `L^k`-blocks. -/
def liftU (hG' : IsLevel G' (k + 1)) (ψ : unitPts G' → Rn N) :
    CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ := fun x i => ψ (unitPt hG' x) i

/-- A fine site of each unit block. -/
noncomputable def unitRep (b : unitPts G') : CTorus d L N₁ m₁ (k + 1) :=
  (unitBlock_surj (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) b.1).choose

theorem unitBlock_unitRep (b : unitPts G') :
    unitBlock (unitRep b) = (b : UnitTorus d L N₁ m₁ k) :=
  (unitBlock_surj (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) b.1).choose_spec

/-- The restriction of a fine field to the unit lattice (evaluation at `unitRep`). -/
noncomputable def unitRestrict (Ψ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ) :
    unitPts G' → Rn N := fun b => WithLp.toLp 2 (fun i => Ψ (unitRep b) i)

theorem isLayerConstant_liftU {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hG : IsLevel G k)
    (hG' : IsLevel G' (k + 1)) (ψ : unitPts G' → Rn N) : IsLayerConstant G (liftU hG' ψ) := by
  intro n hn1 hnk x hx x' hx'
  have hnk' : n = k := by
    have h1 := G.layerIndex_eq hn1 hnk hx
    rw [(hG x).2] at h1
    exact h1.symm
  subst hnk'
  have hb : unitBlock x' = unitBlock x := GeneratingSet.mem_blk.1 hx'
  have hu : unitPt hG' x' = unitPt hG' x := Subtype.ext hb
  funext i
  simp only [liftU, hu]

theorem liftU_unitRestrict {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hG : IsLevel G k)
    (hG' : IsLevel G' (k + 1)) (Ψ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ)
    (hΨ : IsLayerConstant G Ψ) : liftU hG' (unitRestrict (G' := G') Ψ) = Ψ := by
  funext x i
  have hb : unitBlock (unitRep (unitPt hG' x)) = unitBlock x := by
    rw [unitBlock_unitRep]; rfl
  have hx' : x ∈ G.blk k (unitRep (unitPt hG' x)) := GeneratingSet.mem_blk.2 hb.symm
  have hl := hG.mem_layer (unitRep (unitPt hG' x))
  have hk := hG.bounds
  have := congrFun (hΨ k hk.1 hk.2 (unitRep (unitPt hG' x)) hl x hx') i
  simp only [liftU, unitRestrict, PiLp.toLp_apply]
  exact this.symm

end UnitLattice

section Vec

variable (T : Type*) [Fintype T] [DecidableEq T] (N : ℕ)

/-- `(ℝ^N)^T ≃ ℝ^{T × [N]}`. -/
noncomputable def vecEquiv : (T → Rn N) ≃ₗ[ℝ] (T × Fin N → ℝ) where
  toFun x q := x q.1 q.2
  invFun v t := WithLp.toLp 2 (fun i => v (t, i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by funext t; ext i; rfl
  right_inv v := by funext q; rfl

/-- The linear map of `(ℝ^N)^T` given by a real matrix on `T × [N]`. -/
noncomputable def matMap (C : Matrix (T × Fin N) (T × Fin N) ℝ) : (T → Rn N) →ₗ[ℝ] (T → Rn N) :=
  (vecEquiv T N).symm.conj (Matrix.toLin' C)

variable {T N}

theorem matMap_apply (C : Matrix (T × Fin N) (T × Fin N) ℝ) (x : T → Rn N) (t : T) (i : Fin N) :
    matMap T N C x t i = ∑ q : T × Fin N, C (t, i) q * x q.1 q.2 := by
  simp [matMap, LinearEquiv.conj_apply, Matrix.mulVec, dotProduct, vecEquiv]
  rfl

theorem det_matMap (C : Matrix (T × Fin N) (T × Fin N) ℝ) :
    LinearMap.det (matMap T N C) = C.det := by
  unfold matMap
  rw [LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj, LinearMap.det_toLin']

theorem matMap_mul (C D : Matrix (T × Fin N) (T × Fin N) ℝ) (x : T → Rn N) :
    matMap T N C (matMap T N D x) = matMap T N (C * D) x := by
  funext t; ext i
  rw [matMap_apply, matMap_apply]
  simp only [matMap_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
  ring

theorem matMap_one (x : T → Rn N) : matMap T N (1 : Matrix (T × Fin N) (T × Fin N) ℝ) x = x := by
  funext t; ext i
  rw [matMap_apply]
  simp [Matrix.one_apply, Finset.sum_ite_eq]

end Vec

section Setting

variable (d L N₁ m₁ k N : ℕ) [NeZero L] [NeZero N₁] (ϱ : ℝ)

/-- **`𝔹_k` on the step torus**: the whole-lattice generating set of level `k` on the fine torus
`CTorus d L N₁ m₁ (k + 1)` on which the level `k + 1` of `θ` also lives. -/
noncomputable abbrev stepG : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ :=
  levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k (Nat.le_succ k)

/-- **The data of one step** (FLUCTUATION §2.1-§2.6, whole lattice, `λ = ∞`): the block field
`θ`, i.e. the datum `D'` of `𝔹'_k` (level `k + 1`) with its constant field `h`, and the numbers
`a = a₁`, mass `ν` of the backgrounds, `β = β_k` (the multiplier of the Background action, in fine
units), the radius `p₁` of `χ_fl` and the threshold `δ = δ_k` of `χ_k`.  Only typing data. -/
structure StepSetting where
  /-- The generating set of the new level. -/
  G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ
  hk1 : 1 ≤ k
  hG' : IsLevel G' (k + 1)
  /-- The block datum `θ` with its field `h`. -/
  D' : BgData G' N
  h₀ : Fin N → ℝ
  hh₀ : ∀ x i, D'.h x i = (h₀ i : ℂ)
  a₁ : ℝ
  ν : ℝ
  β : ℝ
  p₁ : ℝ
  δ : ℝ

/-- **The terms of the class** at step `k`, on the step torus: `m₀`, the localized terms `Tm` and
the vacuum constant `E_k`. -/
structure StepClass where
  m₀ : ℕ
  Tm : Terms d L N₁ m₁ (k + 1) N ϱ
  Ek : ℝ

end Setting

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- The unit lattice `T^{(k)}_1`. -/
abbrev U : Type := ↥(unitPts S.G')

/-- The fluctuation variables `ψ̂ ∈ (ℝ^N)^{T^{(k)}_1}`; also the space of the old spin `ψ`. -/
abbrev E : Type := S.U → Rn N

include S in
theorem hG : IsLevel (stepG d L N₁ m₁ k ϱ) k := isLevel_levelGS S.hk1 (Nat.le_succ k)

/-- The weights `a_n = a₁ (1 - L⁻²)/(1 - L⁻²ⁿ)` (P2 (4.4)). -/
noncomputable def a : ℕ → ℝ := compWeight L S.a₁

/-- `β_k` in the units of the paper (`η`-units): `β_k^{paper} = β L^{k(d-2)}`. -/
noncomputable def betaU : ℝ := S.β * ((L : ℝ) ^ k) ^ d / ((L : ℝ) ^ k) ^ 2

/-- The number of sites of the unit lattice `T^{(k)}_1`. -/
noncomputable def nU : ℝ := (Fintype.card S.U : ℝ)

/-- `ψ^{(k)}(θ)`, the critical point (2.1). -/
noncomputable def psiKd : BgData (stepG d L N₁ m₁ k ϱ) N :=
  psiK S.hG S.hG' S.a S.ν S.D'

/-- `C^{(k)1/2}` (Lemma 2.4 (c)) at `s = 1`, as a complex matrix on `T^{(k)}_1 × [N]`. -/
noncomputable def covSqrt : Matrix (S.U × Fin N) (S.U × Fin N) ℂ :=
  decCovSqrt S.G' S.a S.a₁ S.ν (bgMult S.G' S.a S.ν S.D') (fun _ => 1)
    (svec S.G' (bgField S.G' S.a S.ν S.D')) (unitQ S.G') (unitP S.G')

/-- `𝒜 = a L⁻² Q*Q + Δ^{(k)}` (Lemma 2.4), so that `C^{(k)} = 𝒜⁻¹`. -/
noncomputable def covA : Matrix (S.U × Fin N) (S.U × Fin N) ℂ :=
  covOp S.G' S.a S.a₁ S.ν (bgMult S.G' S.a S.ν S.D') (svec S.G' (bgField S.G' S.a S.ν S.D'))
    (unitQ S.G') (unitP S.G')

/-- `C^{(k)1/2}` as a linear map of the fluctuation variables (its real entries). -/
noncomputable def K : S.E →ₗ[ℝ] S.E :=
  matMap S.U N (S.covSqrt.map Complex.re)

/-- `C^{(k)-1/2}` as a linear map (the inverse matrix of the real entries of `C^{(k)1/2}`). -/
noncomputable def Kinv : S.E →ₗ[ℝ] S.E :=
  matMap S.U N (S.covSqrt.map Complex.re)⁻¹

/-- The background `ψ^{(k)}(θ)` as a field on the unit lattice. -/
noncomputable def psi0 : S.E := unitRestrict (G' := S.G') (fun x i => ((S.psiKd.Ψ x i).re))

/-- The substitution (2.7): `ψ' = β_k^{-1/2} C^{(k)1/2} ψ̂`, as a field on the unit lattice. -/
noncomputable def shiftU (x : S.E) : S.E := (S.betaU ^ (-(1 / 2 : ℝ))) • S.K x

/-- The old spin `ψ = ψ^{(k)}(θ) + s ψ'(ψ̂)` on the path of the interpolation. -/
noncomputable def psiAt (s : ℝ) (x : S.E) : S.E := S.psi0 + s • S.shiftU x

/-- The datum of the real old spin `ψ` (a field on the unit lattice) with the field `h`. -/
noncomputable def dataU (ψ : S.E) : BgData (stepG d L N₁ m₁ k ϱ) N :=
  realData (stepG d L N₁ m₁ k ϱ) (liftU S.hG' ψ) S.h₀ (isLayerConstant_liftU S.hG S.hG' ψ)

end StepSetting

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

/-! ### The old action, the new action, and the Gaussian kernel `t_k` -/

/-- `A_k(ψ, φ_k(ψ))`: the Background action at the background field of `ψ`. -/
noncomputable def Aold (ψ : S.E) : ℝ :=
  action (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataU ψ)
    (bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataU ψ))

/-- `A^η_{k+1}(θ, φ_{k+1}(θ))`: the action of the new level at the background field of `θ`. -/
noncomputable def Anew : ℝ := action S.G' S.a S.ν S.D' (bgField S.G' S.a S.ν S.D')

/-- The Gaussian coefficient of `t_k` (Definition 2.1): `β_k a L^{d-2}` per block of level `k + 1`,
in the units of the Background action: `β a₁ L^{(k+1)(d-2)}`. -/
noncomputable def cKernel : ℝ :=
  S.β * S.a₁ * (((L : ℝ) ^ (k + 1)) ^ d / ((L : ℝ) ^ (k + 1)) ^ 2)

/-- The number of blocks of level `k + 1`, `|T^{(k+1)}_L| = L^{-d} |T^{(k)}_1|`. -/
noncomputable def nBlocks : ℝ := S.nU / (L : ℝ) ^ d

/-- **The kernel `∏_{z ∈ T^{(k+1)}_L} t_k(θ(z), (Qψ)(z))`** of Definition 2.1, written on the lifted
fields: `(c/2π)^{N |T^{(k+1)}|/2} exp (-β ½ a₁ L^{-2(k+1)} ∑_x |θ - Q_{k+1} ψ|²)`. -/
noncomputable def tKernel (ψ : S.E) : ℝ :=
  (S.cKernel / (2 * Real.pi)) ^ ((N : ℝ) * S.nBlocks / 2) *
    Real.exp (-(S.β * coupling S.G' S.a₁ (k + 1) S.D'.Ψ (S.dataU ψ).Ψ))

/-! ### The density `ρ_k` of the class and the small-field characteristic function `χ^{(k)}` -/

/-- **The density `ρ_k` of (H.1)** (Def-6, complete convention), on real fields of the unit lattice:
`χ_k exp[-β_k A_k(ψ, φ_k(ψ)) + ℰ_k(ψ) - E_k |T^{(k)}_1| + ℱ_k(ψ, g)]`. -/
noncomputable def rhoStep (g : Fld d L N₁ m₁ (k + 1) N) (ψ : S.E) : ℂ :=
  (chiXi (stepG d L N₁ m₁ k ϱ) S.a S.ν S.δ (liftU S.hG' ψ) S.h₀ : ℂ) *
    Complex.exp (-(S.β : ℂ) * (S.Aold ψ : ℂ) +
      EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataU ψ) - (C.Ek : ℂ) * (S.nU : ℂ) +
      FcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataU ψ) g)

/-- **`χ^{(k)} = χ_{(2.2)} χ_fl`** (§2.1): `χ_fl` is evaluated at the fluctuation variable
`ψ̂ = β_k^{1/2} C^{(k)-1/2} (ψ - ψ^{(k)}(θ))`. -/
noncomputable def chiK (ψ : S.E) : ℝ :=
  chi22 S.G' S.δ S.D' (liftU S.hG' ψ) *
    chiFl S.U N S.p₁ ((S.betaU ^ (1 / 2 : ℝ)) • S.Kinv (ψ - S.psi0))

/-- **The fluctuation integral** `(T^{(k)} χ^{(k)} ρ_k)(θ)` (Definition 2.1), the integral over the
old spin `ψ ∈ (ℝ^N)^{T^{(k)}_1}`. -/
noncomputable def Tstep (g : Fld d L N₁ m₁ (k + 1) N) : ℂ :=
  ∫ ψ : S.E, (S.tKernel ψ : ℂ) * (S.chiK ψ : ℂ) * S.rhoStep C g ψ

/-! ### The interaction and the interpolating exponents -/

/-- **The interaction `V^{(k)}(ψ')`** of (2.4), `ψ' = ψ - ψ^{(k)}(θ)`, at the real old spin
`ψ` of the unit lattice: `½⟨α^{(1)}, φ'·φ'⟩ + ½⟨φ₂, H_k φ₂⟩` (landed `interactionV`). -/
noncomputable def Vk (ψ : S.E) : ℂ :=
  interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
    (compTangent S.hG S.hG' (le_refl (k + 1)) S.a (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D'
      (S.dataU ψ))
    (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataU ψ) -
      (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D'))

/-- `δℰ_k(ψ') = ℰ_k(ψ^{(k)} + ψ') - ℰ_k(ψ^{(k)})` as a function of the old spin `ψ`. -/
noncomputable def dE (ψ : S.E) : ℂ :=
  EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataU ψ) -
    EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataU S.psi0)

/-- `δℱ_k(ψ', g) = ℱ_k(ψ^{(k)} + ψ', g) - ℱ_k(ψ^{(k)}, g)`. -/
noncomputable def dF (g : Fld d L N₁ m₁ (k + 1) N) (ψ : S.E) : ℂ :=
  FcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataU ψ) g -
    FcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataU S.psi0) g

/-- **The exponent of `μ_{s,·}`**: `W₁(s, ψ̂) = -β_k V^{(k)}(s ψ') + δℰ_k(s ψ')`,
`ψ' = β_k^{-1/2} C^{(k)1/2} ψ̂`. -/
noncomputable def Wone (s : ℝ) (x : S.E) : ℂ :=
  -(S.β : ℂ) * S.Vk (S.psiAt s x) + S.dE C (S.psiAt s x)

/-- **The exponent of `μ_{·,t}`**: `W₂(t, ψ̂) = δℱ_k(t ψ', g)`. -/
noncomputable def Wtwo (g : Fld d L N₁ m₁ (k + 1) N) (t : ℝ) (x : S.E) : ℂ :=
  S.dF C g (S.psiAt t x)

/-- The fluctuation measure `ν_{p₁} = ⨂_{x ∈ T^{(k)}_1} ν₁` (2.5). -/
noncomputable def nuFl : MeasureTheory.Measure S.E := fluctMeasure S.U N S.p₁

/-- **The partition functions `Z_{s,t}`** of (2.6). -/
noncomputable def Zst (g : Fld d L N₁ m₁ (k + 1) N) (s t : ℝ) : ℂ :=
  partFun₂ S.nuFl (S.Wone C) (S.Wtwo C g) s t

/-- **The interpolating measures `dμ_{s,t}`** of (2.6) for real data (the exponents are real, see
`Wone_real`): `Z_{s,t}^{-1} e^{W₁(s,·) + W₂(t,·)} dν_{p₁}`. -/
noncomputable def muSt (g : Fld d L N₁ m₁ (k + 1) N) (s t : ℝ) : MeasureTheory.Measure S.E :=
  interpMeasure S.nuFl (fun r x => (S.Wone C r x).re) (fun r x => (S.Wtwo C g r x).re) s t

/-! ### The new terms `ℰ₀^{(k+1)}`, `ℱ₀^{(k+1)}`, `ℳ₀^{(k+1)}` and the vacuum constants -/

/-- `½ log det C^{(k)}` (the real part of the determinant of `C^{(k)} = 𝒜⁻¹`). -/
noncomputable def halfLogDetC : ℝ := (1 / 2) * Real.log ((S.covA)⁻¹.det).re

/-- **`ℰ₁^{(k+1)}`** of (2.8): `∫₀¹ ds ∫ dμ_{s,0} ∂_s[-β_k V^{(k)}(s ψ') + δℰ_k(s ψ')]`; the derivative
along the ray is `-β^{1/2}⟨V^{(k)\prime}(β^{-1/2}C^{1/2} s ψ̂), C^{1/2}ψ̂⟩ + β^{-1/2}⟨δℰ_k'(⋯), C^{1/2}ψ̂⟩`. -/
noncomputable def E1 : ℂ :=
  ∫ s in (0 : ℝ)..1, avgFun S.nuFl (S.Wone C) (fun x => deriv (fun r => S.Wone C r x) s) s

/-- **`ℰ₀^{(k+1)} = ½ log det C^{(k)} + ℰ₁^{(k+1)}`** (2.8). -/
noncomputable def E0 : ℂ := (S.halfLogDetC : ℂ) + S.E1 C

/-- **`ℱ₀^{(k+1)}(g)`** of (2.9): `∫₀¹ dt ∫ dμ_{1,t} ∂_t δℱ_k(t ψ', g)`. -/
noncomputable def F0 (g : Fld d L N₁ m₁ (k + 1) N) : ℂ :=
  ∫ t in (0 : ℝ)..1, avgFun₂ S.nuFl (S.Wone C) (S.Wtwo C g)
    (fun x => deriv (fun r => S.Wtwo C g r x) t) 1 t

/-- **`ℳ₀^{(k+1)}(y; g)`** (P4 (2.53)): the vector with `ℱ₀(g) = ⟨g, β_k^{-1/2} ℳ₀(g)⟩₁`, i.e.
`β_k^{1/2} ∫₀¹ dt ∫ dμ_{1,t} ∂_t ℳ_k(y; ψ^{(k)} + t ψ', g)`. -/
noncomputable def M0 (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) : ℂ :=
  ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
    ∫ t in (0 : ℝ)..1, avgFun₂ S.nuFl (S.Wone C) (S.Wtwo C g)
      (fun x => deriv (fun r => McompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
        (S.dataU (S.psiAt r x)) g y i) t) 1 t

/-- `E'_k = E_k - ½ N L^{-d} log (c/2π)` (normalisation of `t_k`; Definition 2.1). -/
noncomputable def Ep : ℝ :=
  C.Ek - (N : ℝ) / 2 * ((L : ℝ) ^ d)⁻¹ * Real.log (S.cKernel / (2 * Real.pi))

/-- `E''_k = E'_k + ½ N log β_k` (the Jacobian of (2.7)). -/
noncomputable def Epp : ℝ := S.Ep C + (N : ℝ) / 2 * Real.log S.betaU

/-- `E'''_k = E''_k - e(N, p₁) - ½ N log 2π` (the normalisation of `ν_{p₁}`, (2.5)). -/
noncomputable def Eppp : ℝ :=
  S.Epp C - fluctE N S.p₁ - (N : ℝ) / 2 * Real.log (2 * Real.pi)

/-! ### Localized forms (P4 (2.56)-(2.60)) -/

/-- The block `B_{k+1}(z)` of the unit lattice over the point `z` of the lattice of level `k + 1`. -/
noncomputable def blockU (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) : Finset S.U :=
  open Classical in Finset.univ.filter fun b => unitBlock1 (b : UnitTorus d L N₁ m₁ k) = z

/-- Restriction of a field of the unit lattice to the block `B_{k+1}(z)` (the scalar products of the
localized forms are restricted to it). -/
noncomputable def maskU (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (x : S.E) : S.E :=
  open Classical in fun b => if b ∈ S.blockU z then x b else 0

/-- `𝕃 = log (a L⁻² Q*Q + Δ^{(k)})` (the logarithm of Lemma 2.4 (c)) as a matrix on `T^{(k)}_1 × [N]`. -/
noncomputable def logA : Matrix (S.U × Fin N) (S.U × Fin N) ℂ :=
  decLog S.G' S.a S.a₁ S.ν (bgMult S.G' S.a S.ν S.D') (fun _ => 1)
    (svec S.G' (bgField S.G' S.a S.ν S.D')) (unitQ S.G') (unitP S.G')

/-- The exponent `W₁(1, ·)` as a function of the shift `ψ'` of the unit lattice. -/
noncomputable def Phi1 (y : S.E) : ℂ :=
  -(S.β : ℂ) * S.Vk (S.psi0 + y) + S.dE C (S.psi0 + y)

/-- **`ℰ₁^{(k+1)}(z)`** (P4 (2.56)-(2.60)): the formula (2.8) with the scalar product restricted to
`y ∈ B_{k+1}(z)`: `∫₀¹ ds ∫ dμ_{s,0} DΦ₁(s ψ')[1_{B(z)} ψ']`. -/
noncomputable def E1loc (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) : ℂ :=
  ∫ s in (0 : ℝ)..1, avgFun S.nuFl (S.Wone C)
    (fun x => (fderiv ℝ (S.Phi1 C) (s • S.shiftU x)) (S.maskU z (S.shiftU x))) s

/-- **`ℰ₀^{(k+1)}(z) = -½ ∑_{y ∈ B(z)} tr 𝕃(y,y) + ℰ₁^{(k+1)}(z)`** (P4 (2.56)). -/
noncomputable def E0loc (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) : ℂ :=
  -(1 / 2 : ℂ) * ∑ y ∈ S.blockU z, ∑ i, S.logA (y, i) (y, i) + S.E1loc C z

end StepSetting

end Balaban.Fluctuation
