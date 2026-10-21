/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7SmallField
public import Balaban.Localization.Decoupled

/-!
# The small-field generating sets of `R` on the Def-6 torus

The old and the new background of P7 (3.22) are those of the small-field generating sets
`𝔹_k(W)`, `W = W_old` or `W_new` (`SFCtx.genW`, on the level-`k` torus `BgT`).  The decoupled
background fields of the localization expansion (P3 §4) live on the torus `CTorus d L N₁ m₁ k` of
the class, which has the same size (`SFCtx.hT`).  This file transports `𝔹_k(W)` to that torus
(`SFCtx.genWC`) and proves the standing hypotheses `DGSetting` of the decoupled theory for it.

The conditions are conditions on the constants of the step:
* `L ^ m₁ ∣ M₁` (the cubes `π¹_j` of side `L^{j+m₁}` of the cover refine the cubes `𝒞_j` of side
  `L^j M₁` of the minimal generating sets, so the layers are cube aligned), `2 ≤ m₁`;
* `4 L² ≤ L^{m₁}` (`DGSetting.hM`);
* `4 d L^{m₁} ≤ 5 M₁` (the separation `5 L M₁` of `𝔹_k(W)` dominates the cover size,
  `DGSetting.cover_sep`);
* `2 d log L ≤ (agmonRate d / 16) (5 L M₁ - 1)` (`DGSetting.sep`);
and the weights and the mass of the background.  `5 < N₁` follows from `L^{m₁} ∣ M₁` and `c ≥ 14`.

* `SFCtx.coarseSide_eq`, `SFCtx.genWC`, `SFCtx.mem_genWC_Ω`;
* `SFCtx.cubeAligned_genWC`, `SFCtx.five_lt_N₁`, `SFCtx.dgSetting_genWC`.
-/

@[expose] public section

namespace Balaban.LargeField.Def7

open Balaban Balaban.Multiscale Balaban.Localization

/-! ### Transport of a generating set along an equality of coarse sides -/

section Cast

variable {d L k : ℕ} [NeZero L]

/-- Transport of a generating set along `N₀ = N₀'`. -/
def castGS {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] {ϱ : ℝ} (h : N₀ = N₀')
    (G : GeneratingSet d L N₀ k ϱ) : GeneratingSet d L N₀' k ϱ := h ▸ G

theorem torusCast_val_eq {a b : ℕ} (h : a = b) (y : Torus d a) (μ : Fin d) :
    ((torusCast h y) μ).val = (y μ).val := by
  subst h
  rfl

theorem mem_castGS_Ω {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] {ϱ : ℝ} (h : N₀ = N₀')
    (h' : N₀' * L ^ k = N₀ * L ^ k) (G : GeneratingSet d L N₀ k ϱ) (j : ℕ)
    (x : Torus d (N₀' * L ^ k)) : x ∈ (castGS h G).Ω j ↔ torusCast h' x ∈ G.Ω j := by
  subst h
  rfl

end Cast

namespace SFCtx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)

/-- The coarse sides of the background torus and of the Def-6 torus agree:
`M₁ (c n_k) = N₁ L^{m₁}` (from `hT`). -/
theorem coarseSide_eq : C.geo.M1 * (C.geo.c * n k) = C.N₁ * S.L ^ m₁ := by
  have h := C.hT
  have hpos : 0 < S.L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _
  exact (Nat.eq_of_mul_eq_mul_right hpos h).symm

instance : NeZero (C.geo.M1 * (C.geo.c * n k)) :=
  ⟨Nat.mul_ne_zero (NeZero.ne _) (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩

instance : NeZero (C.N₁ * S.L ^ m₁) :=
  ⟨Nat.mul_ne_zero (NeZero.ne _) (pow_ne_zero _ (NeZero.ne _))⟩

/-- **The small-field generating set `𝔹_k(W_k)` of `Y` on the Def-6 torus.** -/
noncomputable def genWC (Y : Set (Torus S.d (n k))) :
    GeneratingSet S.d S.L (C.N₁ * S.L ^ m₁) k (minSep S.L C.geo.M1) :=
  castGS C.coarseSide_eq (C.genW Y)

theorem mem_genWC_Ω (Y : Set (Torus S.d (n k))) (j : ℕ)
    (x : Localization.CTorus S.d S.L C.N₁ m₁ k) :
    x ∈ (C.genWC Y).Ω j ↔ sfToBg C.geo C.hT x ∈ (C.genW Y).Ω j :=
  mem_castGS_Ω C.coarseSide_eq C.hT (C.genW Y) j x

/-- The layers of `𝔹_k(W)` are unions of the cubes `𝒞_j` (side `L^j M₁`): membership in `Ω_j`
depends only on the cube index at the level `j`. -/
theorem genW_mem_iff_of_cubeIdx (Y : Set (Torus S.d (n k))) {j : ℕ} (hj : j ≤ k)
    {x x' : BgT C.geo k}
    (h : fineCubeIdx C.geo.M1 (C.geo.c * n k) S.L k j x =
      fineCubeIdx C.geo.M1 (C.geo.c * n k) S.L k j x') :
    x ∈ (C.genW Y).Ω j ↔ x' ∈ (C.genW Y).Ω j := by
  show x ∈ minLayer C.geo.M1 (C.geo.c * n k) S.L k k _ j ↔
    x' ∈ minLayer C.geo.M1 (C.geo.c * n k) S.L k k _ j
  rcases lt_or_eq_of_le hj with h1 | h1
  · rw [minLayer_of_lt _ h1, mem_nearStep, mem_nearStep, h]
  · subst h1
    rw [minLayer_self, mem_cubeInterior, mem_cubeInterior, h]

/-- **Cube alignment of `𝔹_k(W)` on the Def-6 torus**: if `L^{m₁} ∣ M₁`, every layer `Ω_j` is a
union of the cubes of side `L^{j+m₁}`. -/
theorem cubeAligned_genWC (Y : Set (Torus S.d (n k))) (hdvd : S.L ^ m₁ ∣ C.geo.M1)
    (h2 : 2 ≤ m₁) : CubeAligned (C.genWC Y) m₁ where
  two_le := h2
  dvd := dvd_mul_left _ _
  union := by
    intro j _ hjk x x' hxx'
    rw [mem_genWC_Ω, mem_genWC_Ω]
    refine C.genW_mem_iff_of_cubeIdx Y hjk ?_
    have hd : S.L ^ (j + m₁) ∣ S.L ^ j * C.geo.M1 := by
      rw [pow_add]; exact Nat.mul_dvd_mul_left _ hdvd
    obtain ⟨t, ht⟩ := hd
    funext μ
    unfold fineCubeIdx blockMap blockCoord
    have hv : ∀ z : Localization.CTorus S.d S.L C.N₁ m₁ k,
        ((sfToBg C.geo C.hT z) μ).val = (z μ).val := fun z => by
      unfold sfToBg
      exact torusCast_val_eq C.hT z μ
    rw [hv, hv, ht, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hxx' μ]

/-- `5 < N₁`: from `L^{m₁} ∣ M₁` and `c ≥ 14`. -/
theorem five_lt_N₁ (hdvd : S.L ^ m₁ ∣ C.geo.M1) : 5 < C.N₁ := by
  obtain ⟨t, ht⟩ := hdvd
  have h := C.coarseSide_eq
  rw [ht] at h
  have hpos : 0 < S.L ^ m₁ := pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _
  have h' : t * (C.geo.c * n k) = C.N₁ := by
    have : S.L ^ m₁ * (t * (C.geo.c * n k)) = S.L ^ m₁ * C.N₁ := by
      rw [← mul_assoc, h, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have ht0 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · exfalso
      have := C.geo.neM1.out
      rw [ht, h0, mul_zero] at this
      exact this rfl
    · exact h0
  have hn : 1 ≤ n k := Nat.pos_of_ne_zero (NeZero.ne _)
  have hc := C.geo.hc
  rw [← h']
  calc 5 < 14 := by norm_num
    _ ≤ C.geo.c := hc
    _ = 1 * (C.geo.c * 1) := by ring
    _ ≤ t * (C.geo.c * n k) := Nat.mul_le_mul ht0 (Nat.mul_le_mul_left _ hn)

/-- **The standing hypotheses `DGSetting` of the decoupled theory for `𝔹_k(W)` on the Def-6
torus**, from the conditions on the constants (`L^{m₁} ∣ M₁`, `2 ≤ m₁`, `4 L² ≤ L^{m₁}`,
`4 d L^{m₁} ≤ 5 M₁`, the Agmon separation of `5 L M₁`) and the weights and the mass of the
background. -/
theorem dgSetting_genWC (Y : Set (Torus S.d (n k))) {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ S.d)
    (hL : 3 ≤ S.L) (hdvd : S.L ^ m₁ ∣ C.geo.M1) (h2 : 2 ≤ m₁) (hM : 4 * S.L ^ 2 ≤ S.L ^ m₁)
    (hcov : 4 * S.d * S.L ^ m₁ ≤ 5 * C.geo.M1)
    (hsep : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L C.geo.M1 - 1))
    (hw : IsAdmissibleWeights k a) (hν : 0 ≤ ν) (hνL : ν * ((S.L : ℝ) ^ k) ^ 2 ≤ 1) :
    DGSetting (C.genWC Y) a ν where
  hd := hd
  hL := hL
  aligned := C.cubeAligned_genWC Y hdvd h2
  hM := hM
  cover_sep := by
    unfold minSep
    have h : ((4 * S.d * S.L ^ m₁ : ℕ) : ℝ) ≤ ((5 * C.geo.M1 : ℕ) : ℝ) := by exact_mod_cast hcov
    push_cast at h
    have hL0 : (0 : ℝ) ≤ S.L := by positivity
    nlinarith
  sep := hsep
  weights := hw
  mass := hν
  massLe := hνL
  big := C.five_lt_N₁ hdvd

end SFCtx

end Balaban.LargeField.Def7
