/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.BPrimeCubeRoot

/-!
# The cube roots of the residual of `R`: locality

The root of a cube `c` of `𝕋_k` reads the background field `φ̄` at the sites of `c` and their
neighbours (and on the `k`-blocks of `c`, which lie in `c`), the data on the `k`-blocks of `c`, and
the composed fields `ψ^{(j)}` at the sites of `c`.

* `actionGWithCube_congr`, `starBondEWithCube_congr`: the action of a class reads the fields only
  at the sites of the class, their neighbours and the blocks of the class;
* `SFCtx.tCubeOfBg_val`, `SFCtx.tCubeOfBlk_blkMap`: the blocks of level `≤ k` lie in the cubes;
* `SFCtx.cubeRoot_congr_src`, `SFCtx.cubeRoot_congr`: the locality of the root of a cube (in the
  field, the data and the source);
* `SFCtx.dataAgree`: the agreement of data on the `k`-blocks of a region, and `SFCtx.cubeRoot_loc`,
  `SFCtx.cubePair_loc`: a cube root and the pair functional read the fields, the data and the source
  only on a region containing the cube with its neighbours and closed under the `k`-blocks.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.GsSpec

section Generic

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {β : Type*} [DecidableEq β]
  (cs : Site d L N₀ q → β) (cb : ∀ m, Blk d L N₀ q m → β)

/-- **The action of a class reads the fields only at its sites, their neighbours and its blocks.** -/
theorem actionGWithCube_congr (sq : (Fin N → ℂ) → ℂ) (G : GeneratingSet d L N₀ q ϱ)
    (a : ℕ → ℝ) (μ : ℝ) (h : Fin N → ℂ) (X : Finset (Site d L N₀ q)) (c : β)
    {ψ ψ' : (m : ℕ) → Blk d L N₀ q m → Fin N → ℂ} {φ φ' : Site d L N₀ q → Fin N → ℂ}
    (hψ : ∀ m ∈ Finset.Icc 1 q, ∀ y, cb m y = c → ψ m y = ψ' m y)
    (hφ : ∀ x, cs x = c → φ x = φ' x)
    (hφν : ∀ x (ν : Fin d), cs x = c → φ (x + Pi.single ν 1) = φ' (x + Pi.single ν 1))
    (hφb : ∀ m ∈ Finset.Icc 1 q, ∀ y x, cb m y = c → blkMap d L N₀ q m x = y → φ x = φ' x) :
    actionGWithCube cs cb sq G a μ h X ψ φ c = actionGWithCube cs cb sq G a μ h X ψ' φ' c := by
  classical
  unfold actionGWithCube
  have hb : ∀ m ∈ Finset.Icc 1 q, ∀ y, cb m y = c → bavgL d L N₀ q m φ y = bavgL d L N₀ q m φ' y :=
    fun m hm y hy => by
      unfold bavgL bavg
      congr 1
      exact Finset.sum_congr rfl fun x hx => hφb m hm y x hy (mem_blockFibre.1 hx)
  congr 1
  · congr 1
    · congr 1
      refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun y hy => ?_
      have hyc := (Finset.mem_filter.1 hy).2
      rw [hψ m hm y hyc, hb m hm y hyc]
    · congr 1
      refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun x hx => ?_
      have hxc := (Finset.mem_filter.1 hx).2
      unfold bondTermWith
      rw [hφ x hxc, hφν x ν hxc]
  · congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hφ x (Finset.mem_filter.1 hx).2]

/-- **The star bonds of a class read the field only at its sites and their neighbours.** -/
theorem starBondEWithCube_congr (sq : (Fin N → ℂ) → ℂ) (X : Finset (Site d L N₀ q)) (c : β)
    {φ φ' : Site d L N₀ q → Fin N → ℂ} (hφ : ∀ x, cs x = c → φ x = φ' x)
    (hφν : ∀ x (ν : Fin d), cs x = c → φ (x + Pi.single ν 1) = φ' (x + Pi.single ν 1)) :
    starBondEWithCube cs sq X φ c = starBondEWithCube cs sq X φ' c := by
  classical
  unfold starBondEWithCube
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun x hx => ?_
  have hxc := (Finset.mem_filter.1 hx).2
  unfold bondTermWith
  rw [hφ x hxc, hφν x ν hxc]

end Generic

namespace Def7.SFCtx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)

/-- **The coordinates of the cube of `𝕋_k` of a site of the level-`k` torus**: `⌊z_μ / (L^k M)⌋`. -/
theorem tCubeOfBg_val (z : BgT C.geo k) (μ : Fin S.d) :
    (C.tCubeOfBg z μ).val = (z μ).val / (S.L ^ k * M) := by
  have : NeZero (M * n K * S.L ^ K) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne (n K)))
      (pow_ne_zero _ (NeZero.ne S.L))⟩
  unfold tCubeOfBg cubeMap
  rw [blockMap_apply, blockCoord_val (fine_eq (L := S.L) (M := M) (nn := n) C.hnn C.hkK), bgToFine,
    LargeField.torusCast_val]

/-- **A block of level `m ≤ k` lies in the cube of `𝕋_k` of its sites.** -/
theorem tCubeOfBlk_blkMap {m : ℕ} (hm : m ≤ k) (z : BgT C.geo k) :
    C.tCubeOfBlk m (blkMap S.d S.L (C.geo.M1 * (C.geo.c * n k)) k m z) = C.tCubeOfBg z := by
  funext μ
  apply ZMod.val_injective
  have hLm : 0 < S.L ^ m := pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _
  have hside : C.geo.M1 * (C.geo.c * n k) * S.L ^ k =
      S.L ^ m * (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - m)) := by
    have e : S.L ^ k = S.L ^ m * S.L ^ (k - m) := by rw [← pow_add, Nat.add_sub_cancel' hm]
    rw [e]
    ring
  have hblk : ((blkMap S.d S.L (C.geo.M1 * (C.geo.c * n k)) k m z) μ).val = (z μ).val / S.L ^ m := by
    unfold blkMap
    rw [blockMap_apply, blockCoord_val hside]
  have hbase : ((C.blkBase m (blkMap S.d S.L (C.geo.M1 * (C.geo.c * n k)) k m z)) μ).val =
      (z μ).val / S.L ^ m * S.L ^ m := by
    unfold blkBase
    rw [hblk, ZMod.val_natCast_of_lt]
    exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) (ZMod.val_lt _)
  rw [tCubeOfBlk, tCubeOfBg_val, tCubeOfBg_val, hbase]
  have hk : S.L ^ k * M = S.L ^ m * (S.L ^ (k - m) * M) := by
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  rw [hk, ← Nat.div_div_eq_div_mul ((z μ).val / S.L ^ m * S.L ^ m), Nat.mul_div_cancel _ hLm,
    Nat.div_div_eq_div_mul]

/-- The data on the blocks of a cube agree if they agree on its `k`-blocks. -/
theorem psiLevelKOf_congr (c : Torus S.d (n k)) {u u' : BlockAt S n M K k → Fin N → ℂ}
    (h : ∀ y : LargeField.Blk S.d S.L (C.geo.M1 * (C.geo.c * n k)) k k, C.tCubeOfBlk k y = c →
      u (blkToBlock C.geo C.hnn C.hkK y) = u' (blkToBlock C.geo C.hnn C.hkK y)) :
    ∀ m ∈ Finset.Icc 1 k, ∀ y, C.tCubeOfBlk m y = c → C.psiLevelKOf u m y = C.psiLevelKOf u' m y := by
  intro m hm y hy
  unfold psiLevelKOf singleScaleOf
  by_cases hmk : m = k
  · subst hmk
    simp only [le_refl, ↓reduceDIte]
    exact h y hy
  · simp [hmk]

variable (Y : Set (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N))

/-- **Locality of the root of a cube, with two sources**: it depends on `(ψ_k, φ, g)` only through
`φ̄` at the sites of the cube and their neighbours, the data on the `k`-blocks of the cube, the
composed fields at the sites of the cube and the source at the sites of the cube. -/
theorem cubeRoot_congr_src (vc : Def7v2.CorrCoef S.d) (g g' : GIdx S n M K N → ℂ)
    (c : Torus S.d (n k)) {u u' : BlockAt S n M K k → Fin N → ℂ}
    {φ φ' : (C.genW Y).Ω 1 × Fin N → ℂ}
    (hφ : ∀ z : BgT C.geo k, C.tCubeOfBg z = c → C.phiBarAt Y u hv φ z = C.phiBarAt Y u' hv φ' z)
    (hφν : ∀ (z : BgT C.geo k) (ν : Fin S.d), C.tCubeOfBg z = c →
      C.phiBarAt Y u hv φ (z + Pi.single ν 1) = C.phiBarAt Y u' hv φ' (z + Pi.single ν 1))
    (hu : ∀ y : LargeField.Blk S.d S.L (C.geo.M1 * (C.geo.c * n k)) k k, C.tCubeOfBlk k y = c →
      u (blkToBlock C.geo C.hnn C.hkK y) = u' (blkToBlock C.geo C.hnn C.hkK y))
    (hψ : ∀ j ∈ Finset.Icc 1 k, ∀ s, C.tCubeOfC s = c →
      C.psiJAt Y u hv φ j s = C.psiJAt Y u' hv φ' j s)
    (hgc : ∀ z : BgT C.geo k, C.tCubeOfBg z = c → ∀ i,
      g (bgToFine C.geo C.hnn C.hkK z, i) = g' (bgToFine C.geo C.hnn C.hkK z, i)) :
    Def7v2.cubeRoot C vc Y u hv g φ c = Def7v2.cubeRoot C vc Y u' hv g' φ' c := by
  classical
  -- the action of the cube
  have hact : ∀ μ, C.actCube Y u hv μ φ c = C.actCube Y u' hv μ φ' c := by
    intro μ
    unfold actCube
    congr 1
    · refine actionGWithCube_congr C.tCubeOfBg C.tCubeOfBlk _ _ _ _ _ _ c
        (C.psiLevelKOf_congr c hu) hφ hφν ?_
      · intro m hm y z hy hz
        refine hφ z ?_
        rw [← hz, C.tCubeOfBlk_blkMap (Finset.mem_Icc.1 hm).2] at hy
        exact hy
    · rw [starBondEWithCube_congr C.tCubeOfBg _ _ c hφ hφν]
  -- the corrections
  have hcorr : ∀ j ∈ Finset.Icc 1 k, Def7v2.corrCube C vc Y u hv φ j c =
      Def7v2.corrCube C vc Y u' hv φ' j c := by
    intro j hj
    unfold Def7v2.corrCube
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hψ j hj s (Finset.mem_filter.1 hs).2]
  -- the source term
  have hg : Def7v2.gCube C Y u hv g φ c = Def7v2.gCube C Y u' hv g' φ' c := by
    unfold Def7v2.gCube
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
    rw [hφ x (Finset.mem_filter.1 hx).2, hgc x (Finset.mem_filter.1 hx).2 i]
  unfold Def7v2.cubeRoot
  rw [hact, Finset.sum_congr rfl hcorr, hg]

/-- **Locality of the root of a cube**: it depends on `(ψ_k, φ)` only through `φ̄` at the sites of
the cube and their neighbours, the data on the `k`-blocks of the cube and the composed fields at the
sites of the cube. -/
theorem cubeRoot_congr (vc : Def7v2.CorrCoef S.d) (g : GIdx S n M K N → ℂ)
    (c : Torus S.d (n k)) {u u' : BlockAt S n M K k → Fin N → ℂ}
    {φ φ' : (C.genW Y).Ω 1 × Fin N → ℂ}
    (hφ : ∀ z : BgT C.geo k, C.tCubeOfBg z = c → C.phiBarAt Y u hv φ z = C.phiBarAt Y u' hv φ' z)
    (hφν : ∀ (z : BgT C.geo k) (ν : Fin S.d), C.tCubeOfBg z = c →
      C.phiBarAt Y u hv φ (z + Pi.single ν 1) = C.phiBarAt Y u' hv φ' (z + Pi.single ν 1))
    (hu : ∀ y : LargeField.Blk S.d S.L (C.geo.M1 * (C.geo.c * n k)) k k, C.tCubeOfBlk k y = c →
      u (blkToBlock C.geo C.hnn C.hkK y) = u' (blkToBlock C.geo C.hnn C.hkK y))
    (hψ : ∀ j ∈ Finset.Icc 1 k, ∀ s, C.tCubeOfC s = c →
      C.psiJAt Y u hv φ j s = C.psiJAt Y u' hv φ' j s) :
    Def7v2.cubeRoot C vc Y u hv g φ c = Def7v2.cubeRoot C vc Y u' hv g φ' c :=
  C.cubeRoot_congr_src Y hv vc g g c hφ hφν hu hψ fun _ _ _ => rfl

/-! ### The agreement of data on a region -/

/-- The `k`-block (an index of `ψ_k`) of a site of the Def-6 torus. -/
def blkOfC (x : Localization.CTorus S.d S.L C.N₁ m₁ k) : BlockAt S n M K k :=
  blkToBlock C.geo C.hnn C.hkK
    (blkMap S.d S.L (C.geo.M1 * (C.geo.c * n k)) k k (sfToBg C.geo C.hT x))

/-- **The agreement of two data on a region** `A`: they agree on the `k`-blocks of the sites of
`A`. -/
def dataAgree (A : Set (Localization.CTorus S.d S.L C.N₁ m₁ k))
    (u u' : BlockAt S n M K k → Fin N → ℂ) : Prop :=
  ∀ x ∈ A, u (C.blkOfC x) = u' (C.blkOfC x)

theorem dataAgree_refl (A : Set (Localization.CTorus S.d S.L C.N₁ m₁ k))
    (u : BlockAt S n M K k → Fin N → ℂ) : C.dataAgree A u u := fun _ _ => rfl

theorem dataAgree_mono {A A' : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} (hA : A ⊆ A')
    {u u' : BlockAt S n M K k → Fin N → ℂ} (h : C.dataAgree A' u u') : C.dataAgree A u u' :=
  fun x hx => h x (hA hx)

/-- **Data agreeing on a region have the same lifts there** (to any small-field set). -/
theorem liftWC_eq_of_dataAgree {A : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)}
    {u u' : BlockAt S n M K k → Fin N → ℂ} (h : C.dataAgree A u u')
    {x : Localization.CTorus S.d S.L C.N₁ m₁ k} (hx : x ∈ A) (i : Fin N) :
    C.liftWC Y hv u x i = C.liftWC Y hv u' x i := by
  classical
  unfold liftWC
  rw [castTField_apply, castTField_apply]
  unfold liftSingle BgData.clip
  by_cases hz : (GsSpec.torusCast x : BgT C.geo k) ∈ dataSites (C.genW Y)
  · simp only [hz, ↓reduceIte]
    unfold blockLift liftDataC
    have e := h x hx
    unfold blkOfC at e
    rw [sfToBg_eq_torusCast] at e
    exact congrFun e i
  · simp only [hz, ↓reduceIte]

theorem liftAgree_of_dataAgree (Y₁ Y₂ : Set (Torus S.d (n k)))
    {A : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} {u u' : BlockAt S n M K k → Fin N → ℂ}
    (h : C.dataAgree A u u') : C.liftAgree Y₁ Y₂ hv A u u' :=
  fun _ hx i => ⟨C.liftWC_eq_of_dataAgree Y₁ hv h hx i, C.liftWC_eq_of_dataAgree Y₂ hv h hx i⟩

/-- The block of the base site of a `k`-block is the block. -/
theorem blkMap_blkBase (y : LargeField.Blk S.d S.L (C.geo.M1 * (C.geo.c * n k)) k k) :
    blkMap S.d S.L (C.geo.M1 * (C.geo.c * n k)) k k (C.blkBase k y) = y := by
  funext μ
  apply ZMod.val_injective
  have hLk : 0 < S.L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _
  have hside : C.geo.M1 * (C.geo.c * n k) * S.L ^ k =
      S.L ^ k * (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) := by
    rw [Nat.sub_self, pow_zero, mul_one, mul_comm]
  have hval : ((C.blkBase k y) μ).val = (y μ).val * S.L ^ k := by
    unfold blkBase
    rw [ZMod.val_natCast_of_lt]
    have h1 := ZMod.val_lt (y μ)
    have e : C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k) = C.geo.M1 * (C.geo.c * n k) := by
      rw [Nat.sub_self, pow_zero, mul_one]
    have h2 : (y μ).val < C.geo.M1 * (C.geo.c * n k) := lt_of_lt_of_eq h1 e
    exact Nat.mul_lt_mul_of_pos_right h2 hLk
  unfold blkMap
  rw [blockMap_apply, blockCoord_val hside, hval, Nat.mul_div_cancel _ hLk]

theorem sfToBg_torusCast (z : BgT C.geo k) :
    sfToBg C.geo C.hT (GsSpec.torusCast z : Localization.CTorus S.d S.L C.N₁ m₁ k) = z := by
  rw [sfToBg_eq_torusCast, C.torusCast_torusCast_bg]

theorem tCubeOfC_torusCast (z : BgT C.geo k) :
    C.tCubeOfC (GsSpec.torusCast z : Localization.CTorus S.d S.L C.N₁ m₁ k) = C.tCubeOfBg z := by
  unfold tCubeOfC
  rw [C.sfToBg_torusCast]

/-- **Locality of a cube root, with two sources**: for a region `X₁` containing the sites of the
cube, their neighbours and the `k`-blocks of the sites of the cube, the root of the cube for the
region `Y` reads the field, the data and the source `sfG g` only on `X₁`. -/
theorem cubeRoot_loc (vc : Def7v2.CorrCoef S.d) (g g' : GIdx S n M K N → ℂ) (c : Torus S.d (n k))
    {X₁f : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)}
    (hA : ∀ s, C.tCubeOfC s = c → ∀ y, SameCell (S.L ^ k) y s → y ∈ X₁f)
    (hAν : ∀ (z : BgT C.geo k) (ν : Fin S.d), C.tCubeOfBg z = c →
      (GsSpec.torusCast (z + Pi.single ν 1) : Localization.CTorus S.d S.L C.N₁ m₁ k) ∈ X₁f)
    (u u' : BlockAt S n M K k → Fin N → ℂ) (φ φ' : (C.genWC Y).Ω 1 × Fin N → ℂ)
    (hφ : ∀ y : (C.genWC Y).Ω 1, (y : Localization.CTorus S.d S.L C.N₁ m₁ k) ∈ X₁f →
      ∀ i, φ (y, i) = φ' (y, i))
    (hu : C.dataAgree ↑X₁f u u')
    (hg : ∀ x ∈ (X₁f : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)), ∀ i,
      sfG C.geo C.hnn C.hkK C.hT g x i = sfG C.geo C.hnn C.hkK C.hT g' x i) :
    Def7v2.cubeRoot C vc Y u hv g (castΩField C.coarseSide_eq (C.genW Y) φ) c =
      Def7v2.cubeRoot C vc Y u' hv g' (castΩField C.coarseSide_eq (C.genW Y) φ') c := by
  classical
  have hcube : ∀ z : BgT C.geo k, C.tCubeOfBg z = c →
      (GsSpec.torusCast z : Localization.CTorus S.d S.L C.N₁ m₁ k) ∈ X₁f := fun z hz =>
    hA _ (by rw [C.tCubeOfC_torusCast, hz]) _ (SameCell.refl _ _)
  have hbar : ∀ x ∈ X₁f, ∀ i, barField (C.genWC Y) (C.liftWC Y hv u) φ x i =
      barField (C.genWC Y) (C.liftWC Y hv u') φ' x i := by
    intro x hx i
    unfold barField
    by_cases hxΩ : x ∈ (C.genWC Y).Ω 1
    · simp only [hxΩ, ↓reduceDIte]
      exact hφ ⟨x, hxΩ⟩ hx i
    · simp only [hxΩ, ↓reduceDIte]
      exact C.liftWC_eq_of_dataAgree Y hv hu hx i
  refine C.cubeRoot_congr_src Y hv vc g g' c ?_ ?_ ?_ ?_ ?_
  · intro z hz
    funext i
    rw [C.phiBarAt_cast Y hv, C.phiBarAt_cast Y hv]
    exact hbar _ (hcube z hz) i
  · intro z ν hz
    funext i
    rw [C.phiBarAt_cast Y hv, C.phiBarAt_cast Y hv]
    exact hbar _ (hAν z ν hz) i
  · intro y hy
    have hx := hcube (C.blkBase k y) hy
    have e := hu _ hx
    unfold blkOfC at e
    rw [C.sfToBg_torusCast, C.blkMap_blkBase] at e
    exact e
  · intro j hj s hs
    have hjk : j ≤ k := (Finset.mem_Icc.1 hj).2
    funext i
    rw [C.psiJAt_cast Y u hv φ hjk s i, C.psiJAt_cast Y u' hv φ' hjk s i]
    refine composeField_congr C.weights (fun y hy i' => ?_) (fun i' => ?_) i
    · exact svec_eq_of_agree hφ (hA s hs y (composeDep_sameCell hy)) i'
    · exact C.liftWC_eq_of_dataAgree Y hv hu (hA s hs s (SameCell.refl _ _)) i'
  · intro z hz i
    have e := hg _ (hcube z hz) i
    unfold sfG at e
    rw [C.sfToBg_torusCast] at e
    exact e

variable (Y₁ Y₂ : Set (Torus S.d (n k)))

/-- **Locality of the pair functional of a cube root**: for a region `X₁` containing the sites of the
cube, their neighbours and the `k`-blocks of the sites of the cube, it reads the two fields and the
data only on `X₁`. -/
theorem cubePair_loc (vc : Def7v2.CorrCoef S.d) (g : GIdx S n M K N → ℂ) (c : Torus S.d (n k))
    {X₁f : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)}
    (hA : ∀ s, C.tCubeOfC s = c → ∀ y, SameCell (S.L ^ k) y s → y ∈ X₁f)
    (hAν : ∀ (z : BgT C.geo k) (ν : Fin S.d), C.tCubeOfBg z = c →
      (GsSpec.torusCast (z + Pi.single ν 1) : Localization.CTorus S.d S.L C.N₁ m₁ k) ∈ X₁f)
    (u u' : BlockAt S n M K k → Fin N → ℂ) (φ₁ φ₁' : (C.genWC Y₁).Ω 1 × Fin N → ℂ)
    (φ₂ φ₂' : (C.genWC Y₂).Ω 1 × Fin N → ℂ)
    (h₁ : ∀ y : (C.genWC Y₁).Ω 1, (y : Localization.CTorus S.d S.L C.N₁ m₁ k) ∈ X₁f →
      ∀ i, φ₁ (y, i) = φ₁' (y, i))
    (h₂ : ∀ y : (C.genWC Y₂).Ω 1, (y : Localization.CTorus S.d S.L C.N₁ m₁ k) ∈ X₁f →
      ∀ i, φ₂ (y, i) = φ₂' (y, i))
    (hu : C.dataAgree ↑X₁f u u') :
    C.cubePair hv Y₁ Y₂ vc g c u φ₁ φ₂ = C.cubePair hv Y₁ Y₂ vc g c u' φ₁' φ₂' := by
  unfold cubePair
  rw [C.cubeRoot_loc Y₁ hv vc g g c hA hAν u u' φ₁ φ₁' h₁ hu (fun _ _ _ => rfl),
    C.cubeRoot_loc Y₂ hv vc g g c hA hAν u u' φ₂ φ₂' h₂ hu (fun _ _ _ => rfl)]

end Def7.SFCtx

end Balaban.LargeField
