/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.PsiZeroWitnessDen
public import Balaban.LargeField.R.CancelBound

/-!
# A concrete instance of `cancellation_identity` (Lemma III.6.3)

On top of the instance of `PsiZeroWitness` (`d ≥ 3`, `L ≥ 3`, `N₁ ≥ 4`, `k ≥ 2`; concretely `d = 3`, `L = 3`,
`N₁ = 6`, `m₁ = 0`, `k = 2`; reference `ψ⁰_k ≡ e₀` on the box `box 0 (2,…,2)`), the window data:

* `G = 𝔹_1 = levelGS 1 ≺ 𝔹_k = G'` (every site has layer index `1 < k`, so `hZb` holds);
* `Du = lift(e₁)`, `e₁ = (0,1)`, with `(φ_u, α_u) = (bgField, bgMult)` and `IsEL` from `theorem71`;
  its spin differs from the reference `e₀` on every block: `Q_zδψ = e₁ - e₀ = (-1, 1)`;
* `Z_b = {z₀}`, `z₀` the block with all coordinates `2` (outside the box), `D = X_win = fib z₀`
  (`D₀ = D_ω = ∅`; `D_ω = ∅` since no site of `𝔹_1` has layer index `k`), `Z_{k₁} = fib b₀`
  (`b₀` a block of the box), `Z = D ⊔ Z_{k₁}`, `a^♮_z = a_z`, `ϖ ≡ 1`.

Results: `cancellation_identity_hyps_nonempty` (all hypotheses hold), `gauss_term_witness` (the Gaussian term
is `β_k a_{z₀} > 0`), `Cnat1_witness`, `Cnat0_witness` (explicit constants `(36, 8, 9, 1)`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField.Def6 Balaban.Fluctuation
  Balaban.Inhabited MeasureTheory Matrix ActionConv

namespace PsiZeroWitness

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- The window generating set `𝔹_1 = levelGS 1`. -/
noncomputable def Gw (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] (hk : 1 ≤ k) :
    GeneratingSet d L (N₁ * L ^ m₁) k (ϱ d L) :=
  levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ d L) 1 hk

theorem precW (hk : 1 ≤ k) : Precedes (Gw d L N₁ m₁ k hk) (G d L N₁ m₁ k) := levelGS_precedes hk

theorem gw_mem (hk : 1 ≤ k) (x : Torus d (N₁ * L ^ m₁ * L ^ k)) : x ∈ (Gw d L N₁ m₁ k hk).Ω 1 := by
  simp [Gw, levelGS]

theorem gw_layer (hk : 1 ≤ k) (x : Torus d (N₁ * L ^ m₁ * L ^ k)) :
    (Gw d L N₁ m₁ k hk).layerIndex x = 1 := (isLevel_levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ d L) le_rfl hk x).2

theorem G_layer (hk : 1 ≤ k) (x : Torus d (N₁ * L ^ m₁ * L ^ k)) :
    (G d L N₁ m₁ k).layerIndex x = k := (isLevel_G hk x).2

/-- The region of a generating set consisting of the sites of the given `k`-blocks. -/
noncomputable def regionOf {ϱ ϱ' : ℝ} {N₀ : ℕ} [NeZero N₀] {G : GeneratingSet d L N₀ k ϱ}
    {G' : GeneratingSet d L N₀ k ϱ'} (hprec : Precedes G G') (hΩ : ∀ x, x ∈ G.Ω 1)
    (hl : ∀ x, G'.layerIndex x = k) (S : Finset (Torus d (N₀ * L ^ (k - k)))) : Region G where
  sites := S.biUnion (fib d L N₀ k k)
  sub_Ω := fun x _ => hΩ x
  blockClosed := by
    intro x hx y hy
    have hy' := blk_subset_blk' hprec (hΩ x) hy
    rw [hl x] at hy'
    have hjb : jBlock d L N₀ k k y = jBlock d L N₀ k k x := GeneratingSet.mem_blk.1 hy'
    obtain ⟨z, hz, hxz⟩ := Finset.mem_biUnion.1 hx
    exact Finset.mem_biUnion.2 ⟨z, hz, mem_fib.2 (hjb.trans (mem_fib.1 hxz))⟩

theorem regionOf_sites {ϱ ϱ' : ℝ} {N₀ : ℕ} [NeZero N₀] {G : GeneratingSet d L N₀ k ϱ}
    {G' : GeneratingSet d L N₀ k ϱ'} (hprec : Precedes G G') (hΩ : ∀ x, x ∈ G.Ω 1)
    (hl : ∀ x, G'.layerIndex x = k) (S : Finset (Torus d (N₀ * L ^ (k - k)))) :
    (regionOf hprec hΩ hl S).sites = S.biUnion (fib d L N₀ k k) := rfl

theorem hN2' : (0 : ℕ) < 2 := by norm_num

theorem psiZeroData_ψ0W :
    psiZeroData (G d L N₁ m₁ k) (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
      (fun _ => (0 : ℝ)) = unitBg (G d L N₁ m₁ k) hN2' (fun _ => 0) := by
  rw [← dataR_constBlock]
  unfold psiZeroData dataR dataC
  congr 1

theorem bgField_unitW (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hk : 1 ≤ k) :
    bgField (G d L N₁ m₁ k) (a L) 0 (unitBg (G d L N₁ m₁ k) hN2' (fun _ => 0)) =
      unitPhi (G d L N₁ m₁ k) hN2' := by
  have hc1 : 0 < bgC1 d L 2 := Balaban.Localization.bgC1_pos' (d := d) (L := L) (N := 2) (by omega)
  have hD : InUnionDomainR (G d L N₁ m₁ k) (bgC1 d L 2) 0
      (unitBg (G d L N₁ m₁ k) hN2' (fun _ => 0)) := by
    rw [← dataR_constBlock]
    exact inUnionDomainR_of_tube _ hc1 le_rfl (tube_constBlock _ hN2' hc1 Set.univ)
  exact bgField_unitBg (isLevel_G hk) hN2' (fun _ => compWeight_nonneg (by omega) one_pos _) _
    (H hd3 hL) hD

theorem phiZero_ψ0W (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hk : 1 ≤ k) :
    phiZero (G d L N₁ m₁ k) (a L) (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
      (fun _ => (0 : ℝ)) = unitPhi (G d L N₁ m₁ k) hN2' := by
  unfold phiZero
  rw [psiZeroData_ψ0W]
  exact bgField_unitW hd3 hL hk

theorem windowΨ_ψ0W (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hk : 1 ≤ k) (x : Torus d (N₁ * L ^ m₁ * L ^ k))
    (i : Fin 2) :
    (windowData (Gw d L N₁ m₁ k hk) (G d L N₁ m₁ k) (precW hk) (a L)
      (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) (fun _ => (0 : ℝ))).Ψ x i =
      (unitVec hN2' i : ℂ) := by
  have hx : x ∈ dataSites (Gw d L N₁ m₁ k hk) := (mem_dataSites _).2 (Or.inl (gw_mem hk x))
  have hD : (unitBg (G d L N₁ m₁ k) hN2' (fun _ => 0)).Ψ x i = (unitVec hN2' i : ℂ) :=
    unitBg_Ψ_of_mem (G d L N₁ m₁ k) hN2' _ ((mem_dataSites _).2 (Or.inl (isLevel_G hk x).1)) i
  have hc : ∀ (H : GeneratingSet d L (N₁ * L ^ m₁) k (ϱ d L)) (n : ℕ) (hn : n ≤ k),
      blockMean H n (fun y => svec (G d L N₁ m₁ k) (unitPhi (G d L N₁ m₁ k) hN2') y i) x =
        (unitVec hN2' i : ℂ) := by
    intro H n hn
    have : (fun y => svec (G d L N₁ m₁ k) (unitPhi (G d L N₁ m₁ k) hN2') y i) =
        fun _ => (unitVec hN2' i : ℂ) := funext fun y => svec_unitPhi (isLevel_G hk) hN2' y i
    rw [this]
    exact blockMean_const H hn _ x
  have e : psiZeroWin (Gw d L N₁ m₁ k hk) (G d L N₁ m₁ k) (a L)
      (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) (fun _ => (0 : ℝ)) x i =
      (unitVec hN2' i : ℂ) := by
    unfold psiZeroWin
    rw [composeField_of_mem _ _ _ (gw_mem hk x), psiZeroData_ψ0W, bgField_unitW hd3 hL hk]
    rw [hc (Gw d L N₁ m₁ k hk) _ (by rw [gw_layer hk]; exact hk),
      hc (G d L N₁ m₁ k) _ (by rw [G_layer hk]), hD]
    simp
  unfold windowData
  simp only [BgData.clip, hx, ↓reduceIte]
  exact e

theorem hk1 (h : 2 ≤ k) : 1 ≤ k := by omega

/-- The block datum `e₁ = (0, 1)` (constant), a rotation of the reference `e₀` by `π/2`. -/
def ψc (d L N₁ m₁ k : ℕ) : BlockField d L (N₁ * L ^ m₁) k 2 := fun _ => ![0, 1]

theorem tube_ψc {ϱ : ℝ} (G' : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) {δ : ℝ} (hδ : 0 < δ)
    (Y : Set (Torus d (N₁ * L ^ m₁ * L ^ (k - k)))) : TubeOn G' Y δ (ψc d L N₁ m₁ k) := by
  refine ⟨fun x x' _ _ _ => ?_, fun x _ _ => ?_⟩
  · simpa [rn, liftR, ψc] using hδ
  · simpa [ψc, Fin.sum_univ_two] using hδ

/-- The datum `Du = lift(e₁)` of the window generating set `𝔹_1`: the constant block spin `e₁`. -/
noncomputable def DuW (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] (hk : 1 ≤ k) :
    BgData (Gw d L N₁ m₁ k hk) 2 := dataR (Gw d L N₁ m₁ k hk) (ψc d L N₁ m₁ k)

/-- The Euler-Lagrange pair of `Du`: the background field `φ_{k₁,k}`. -/
noncomputable def phiU (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] (hk : 1 ≤ k) :
    (Gw d L N₁ m₁ k hk).Ω 1 × Fin 2 → ℂ :=
  bgField (Gw d L N₁ m₁ k hk) (a L) 0 (DuW d L N₁ m₁ k hk)

/-- The multiplier of `φ_{k₁,k}`. -/
noncomputable def alphaU (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] (hk : 1 ≤ k) :
    (Gw d L N₁ m₁ k hk).Ω 1 → ℂ :=
  bgMult (Gw d L N₁ m₁ k hk) (a L) 0 (DuW d L N₁ m₁ k hk)

theorem isEL_DuW (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hk : 1 ≤ k) :
    IsEL (Gw d L N₁ m₁ k hk) (compWeight L 1) 0 (DuW d L N₁ m₁ k hk) (phiU d L N₁ m₁ k hk)
      (alphaU d L N₁ m₁ k hk) := by
  have hc1 : 0 < bgC1 d L 2 := Balaban.Localization.bgC1_pos' (d := d) (L := L) (N := 2) (by omega)
  have hD : InUnionDomainR (Gw d L N₁ m₁ k hk) (bgC1 d L 2) 0 (DuW d L N₁ m₁ k hk) :=
    inUnionDomainR_of_tube _ hc1 le_rfl (tube_ψc _ hc1 Set.univ)
  exact (theorem71 (H hd3 hL) hD).2.2.1.1

/-- The two `k`-blocks: `z₀` (the slab `z_i = 2`, outside the box) carries `Z_b`; `z₁ = b₀` (a block of
the box) carries `Z_{k₁}`. -/
def z0W (d L N₁ m₁ k : ℕ) : Torus d (N₁ * L ^ m₁ * L ^ (k - k)) := fun _ => 2

theorem z0W_ne (hd : 0 < d) (hN : 4 ≤ N₁) : z0W d L N₁ m₁ k ≠ b0 d L N₁ m₁ k := by
  have hn : 4 ≤ N₁ * L ^ m₁ * L ^ (k - k) := by
    have : 1 ≤ L ^ m₁ := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
    simp only [Nat.sub_self, pow_zero, mul_one]
    nlinarith
  have h20 : (2 : ZMod (N₁ * L ^ m₁ * L ^ (k - k))) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ (k - k))) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  intro h
  exact h20 (congrFun h ⟨0, hd⟩)

theorem b0_mem_box (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] :
    b0 d L N₁ m₁ k ∈ box (b0 d L N₁ m₁ k) (w d) := fun i => ⟨0, by simp [w], by simp⟩

theorem precG (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] : Precedes (G d L N₁ m₁ k) (G d L N₁ m₁ k) :=
  fun _ _ _ => subset_rfl

/-- `D = X_win`: the sites of the block `z₀` (so `D₀ = D_ω = ∅`, `Z_b = {z₀}`). -/
noncomputable def DW (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] (hk : 1 ≤ k) : Region (Gw d L N₁ m₁ k hk) :=
  regionOf (precW hk) (gw_mem hk) (G_layer hk) {z0W d L N₁ m₁ k}

/-- `Z_{k₁}`: the sites of the box block `b₀`. -/
noncomputable def Zk1W (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] (hk : 1 ≤ k) : Region (G d L N₁ m₁ k) :=
  regionOf (precG d L N₁ m₁ k) (fun x => (isLevel_G hk x).1) (G_layer hk) {b0 d L N₁ m₁ k}

/-- `Z = X_win ⊔ Z_{k₁}`. -/
noncomputable def ZrW (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] (hk : 1 ≤ k) : Region (G d L N₁ m₁ k) :=
  regionOf (precG d L N₁ m₁ k) (fun x => (isLevel_G hk x).1) (G_layer hk)
    {z0W d L N₁ m₁ k, b0 d L N₁ m₁ k}

theorem ZrW_sites (hk : 1 ≤ k) : (ZrW d L N₁ m₁ k hk).sites =
    (DW d L N₁ m₁ k hk).sites ∪ (Zk1W d L N₁ m₁ k hk).sites := by
  simp [ZrW, DW, Zk1W, regionOf_sites]

theorem DW_disjoint (hd : 0 < d) (hN : 4 ≤ N₁) (hk : 1 ≤ k) :
    Disjoint (DW d L N₁ m₁ k hk).sites (Zk1W d L N₁ m₁ k hk).sites := by
  unfold DW Zk1W
  rw [regionOf_sites, regionOf_sites, Finset.singleton_biUnion, Finset.singleton_biUnion]
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact z0W_ne (L := L) (m₁ := m₁) (k := k) hd hN ((mem_fib.1 hx).symm.trans (mem_fib.1 hx'))

/-- `ψ_k(z) = ψ⁰_k(z)` as a complex block field (the reference `e₀`). -/
noncomputable def ψkW (d L N₁ m₁ k : ℕ) : Torus d (N₁ * L ^ m₁ * L ^ (k - k)) → Fin 2 → ℂ :=
  fun z i => ((ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ⟨k, z⟩ i : ℝ) : ℂ)

/-- The layer factors `ϖ ≡ 1`. -/
def ϖW : ℕ → ℝ := fun _ => 1

/-- The external field `h = 0`. -/
def hW : Fin 2 → ℝ := fun _ => 0

/-- The weights `a^♮_z = a_z` (the ideal composed weight). -/
noncomputable def aNW (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] (hk : 1 ≤ k) :
    Torus d (N₁ * L ^ m₁ * L ^ (k - k)) → ℝ := compWeightZ (Gw d L N₁ m₁ k hk) 1

/-- The window datum `ψ⁰_{k₁,k}` of the instance. -/
noncomputable def winW (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] (hk : 1 ≤ k) :
    BgData (Gw d L N₁ m₁ k hk) 2 :=
  windowData (Gw d L N₁ m₁ k hk) (G d L N₁ m₁ k) (precW hk) (compWeight L 1)
    (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) hW

/-- **The identity of `cancellation_identity` at the instance** (the conclusion of the landed theorem with the
data `G = 𝔹_1`, `G' = 𝔹_k`, `a₁ = 1`, `Du = DuW`, `D = DW`, `Zr = ZrW`, `Zk1 = Zk1W`, `D₀ = D_ω = ∅`,
`Z_b = {z₀}`). -/
noncomputable def CancelIdentityStmt (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] (hk : 1 ≤ k) (β0 ν : ℝ) :
    Prop :=
  gaussNat (Gw d L N₁ m₁ k hk) ϖW (DuW d L N₁ m₁ k hk).Ψ (betaK d L k β0) (aNW d L N₁ m₁ k hk)
      (ψkW d L N₁ m₁ k) {z0W d L N₁ m₁ k} +
    (β0 : ℂ) * actionRegionC (DW d L N₁ m₁ k hk) (compWeight L 1) ν (DuW d L N₁ m₁ k hk)
      (phiU d L N₁ m₁ k hk) -
    ((Real.log (constNat 2 (betaK d L k β0) (aNW d L N₁ m₁ k hk) {z0W d L N₁ m₁ k}) : ℝ) : ℂ) =
  (β0 : ℂ) * actionRegionC (ZrW d L N₁ m₁ k hk) (compWeight L 1) ν
        (psiZeroData (G d L N₁ m₁ k) (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) hW)
        (phiZero (G d L N₁ m₁ k) (compWeight L 1) (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) hW) -
    (β0 : ℂ) * actionRegion0 (Zk1W d L N₁ m₁ k hk) ν
        (psiZeroData (G d L N₁ m₁ k) (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) hW)
        (phiZero (G d L N₁ m₁ k) (compWeight L 1) (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) hW) +
    ((betaK d L k β0 : ℝ) * ∑ z ∈ ({z0W d L N₁ m₁ k} : Finset _), (1 / 2 : ℂ) * (aNW d L N₁ m₁ k hk z : ℂ) *
          dotC (kAvg (dataInc (winW d L N₁ m₁ k hk) (DuW d L N₁ m₁ k hk)) z)
            (kAvg (dataInc (winW d L N₁ m₁ k hk) (DuW d L N₁ m₁ k hk)) z) +
      (β0 : ℂ) * (deltaActionC (DW d L N₁ m₁ k hk) (compWeight L 1) ν (winW d L N₁ m₁ k hk)
            (DuW d L N₁ m₁ k hk)
            ((precW hk).restrictφ (phiZero (G d L N₁ m₁ k) (compWeight L 1)
              (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) hW))
            (phiU d L N₁ m₁ k hk)
            ((precW hk).restrictα (alphaZero (G d L N₁ m₁ k) (compWeight L 1)
              (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) hW)) +
        nuTerm (DW d L N₁ m₁ k hk) ν (winW d L N₁ m₁ k hk)
          ((precW hk).restrictφ (phiZero (G d L N₁ m₁ k) (compWeight L 1)
            (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) hW))
          (phiU d L N₁ m₁ k hk))) +
    (β0 : ℂ) * stTerm (DW d L N₁ m₁ k hk) (winW d L N₁ m₁ k hk) (DuW d L N₁ m₁ k hk)
        ((precW hk).restrictφ (phiZero (G d L N₁ m₁ k) (compWeight L 1)
          (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) hW))
        (phiU d L N₁ m₁ k hk) -
    ((Real.log (constNat 2 (betaK d L k β0) (compWeightZ (Gw d L N₁ m₁ k hk) 1)
      {z0W d L N₁ m₁ k}) : ℝ) : ℂ) +
    Cnat 1 (precW hk) (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) hW
      (DuW d L N₁ m₁ k hk) {z0W d L N₁ m₁ k} β0 ϖW (aNW d L N₁ m₁ k hk) (ψkW d L N₁ m₁ k)

theorem hZbW (hk2 : 2 ≤ k) : ∀ z ∈ ({z0W d L N₁ m₁ k} : Finset _), ∀ x ∈ fib d L (N₁ * L ^ m₁) k k z,
    1 ≤ (Gw d L N₁ m₁ k (hk1 hk2)).layerIndex x ∧ (Gw d L N₁ m₁ k (hk1 hk2)).layerIndex x < k := by
  intro z _ x _
  rw [gw_layer]
  exact ⟨le_rfl, by omega⟩

/-- **`cancellation_identity` (Lemma III.6.3) has a concrete non-vacuous instance**: `d ≥ 3`, `L ≥ 3`,
`k ≥ 2`, `N₁ ≥ 4`: the reference `ψ⁰_k ≡ e₀` of `PsiZeroWitness` on the box `box 0 (2,…,2)`, the window
generating set `𝔹_1 ≺ 𝔹_k`, the datum `Du = lift(e₁)` (`e₁ = (0,1)`) with its Euler-Lagrange pair, the regions
`D = X_win = fib z₀`, `Z_{k₁} = fib b₀`, `Z = D ⊔ Z_{k₁}`, `D₀ = D_ω = ∅`, `Z_b = {z₀}`. -/
theorem cancellation_identity_hyps_nonempty (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hN : 4 ≤ N₁) (hk2 : 2 ≤ k)
    {β0 : ℝ} (ν : ℝ) (hβ0 : 0 < β0) : CancelIdentityStmt d L N₁ m₁ k (hk1 hk2) β0 ν := by
  have hk := hk1 hk2
  obtain ⟨δ, hδ, hδc, hKδ⟩ := small_delta (m₁ := m₁) hd3 hL hN hk
  have hZ := hZbW (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hk2
  refine ActionConv.cancellation_identity (a₁ := 1) (D' := 2) (by omega) hk one_pos hβ0
    (b0 d L N₁ m₁ k) (w d) (hw1 d) (hwD d) (hm hN) (hXreg d L N₁ m₁ k) (hΩ d L N₁ m₁ k)
    (hdata d L N₁ m₁ k) (H hd3 hL) hδ hδc (tube_ψk hδ _) hKδ (precW hk)
    (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) hW (hψ0W hd3 hL hN hk hδ hδc)
    (DuW d L N₁ m₁ k hk) ?_ (isEL_DuW hd3 hL hk) (DW d L N₁ m₁ k hk) (ZrW d L N₁ m₁ k hk)
    (Zk1W d L N₁ m₁ k hk) ∅ ∅ {z0W d L N₁ m₁ k} ?_ (by simp) (by simp) (ZrW_sites hk)
    (DW_disjoint (by omega) hN hk) (fun x _ => G_layer hk x) (by simp) ?_ (by simp) hZ
    (ψkW d L N₁ m₁ k) (fun _ _ _ => rfl) ϖW (aNW d L N₁ m₁ k hk) ?_
  · intro x i
    rw [DuW, dataR_h _ _ (gw_mem hk x) i]
    unfold windowData hW
    simp [BgData.clip, gw_mem hk x]
  · unfold DW
    rw [regionOf_sites]
    simp
  · intro x hx
    unfold Zk1W at hx
    rw [regionOf_sites, Finset.singleton_biUnion] at hx
    have := mem_fib.1 hx
    rw [show jBlock d L (N₁ * L ^ m₁) k k x = b0 d L N₁ m₁ k from this]
    exact b0_mem_box d L N₁ m₁ k
  · intro z hz
    exact compWeightZ_pos one_pos (by omega) _ (hZ z hz)

/-! ### Non-degeneracy and the remainder bounds -/

theorem kAvg_const_W {N₀ : ℕ} [NeZero N₀] (v : Fin 2 → ℂ) (z : Torus d (N₀ * L ^ (k - k)))
    (i : Fin 2) : kAvg (d := d) (L := L) (N₀ := N₀) (k := k) (fun _ j => v j) z i = v i := by
  have h : ((fib d L N₀ k k z).card : ℝ) = blockVol d L k := by
    rw [card_fib le_rfl, blockVol_eq]; push_cast; rfl
  have hV : (blockVol d L k : ℝ) ≠ 0 := (blockVol_pos (d := d) (k := k) (NeZero.pos L)).ne'
  have h' : ((fib d L N₀ k k z).card : ℂ) = (blockVol d L k : ℂ) := by exact_mod_cast h
  have hV' : (blockVol d L k : ℂ) ≠ 0 := by exact_mod_cast hV
  unfold kAvg
  rw [Finset.sum_const, nsmul_eq_mul, h']
  field_simp

/-- The vector `e₁ - e₀ = (-1, 1)`: the increment `Du - ψ⁰_{k₁,k}` of the window datum. -/
noncomputable def vInc : Fin 2 → ℂ := fun i => ((![0, 1] i : ℝ) : ℂ) - (unitVec hN2' i : ℂ)

theorem dataInc_W (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hk : 1 ≤ k) (x : Torus d (N₁ * L ^ m₁ * L ^ k))
    (i : Fin 2) :
    dataInc (winW d L N₁ m₁ k hk) (DuW d L N₁ m₁ k hk) x i = vInc i := by
  have hx : x ∈ dataSites (Gw d L N₁ m₁ k hk) := (mem_dataSites _).2 (Or.inl (gw_mem hk x))
  unfold dataInc
  rw [show (winW d L N₁ m₁ k hk).Ψ x i = (unitVec hN2' i : ℂ) from windowΨ_ψ0W hd3 hL hk x i,
    DuW, dataR_Ψ _ _ hx]
  simp [vInc, liftR, ψc]

theorem kAvg_inc_W (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hk : 1 ≤ k) (z : Torus d (N₁ * L ^ m₁ * L ^ (k - k))) :
    kAvg (dataInc (winW d L N₁ m₁ k hk) (DuW d L N₁ m₁ k hk)) z = vInc := by
  have : dataInc (winW d L N₁ m₁ k hk) (DuW d L N₁ m₁ k hk) = fun _ j => vInc j :=
    funext fun x => funext fun i => dataInc_W hd3 hL hk x i
  funext i
  rw [this]
  exact kAvg_const_W vInc z i

theorem dot_vInc : dotC vInc vInc = 2 := by
  simp [dotC, vInc, Fin.sum_univ_two, unitVec]
  norm_num

/-- **Non-degeneracy**: the Gaussian quadratic term `β_k Σ_z ½ a^♮_z Q_zδψ·Q_zδψ` of the instance equals
`β_k a^♮_{z₀} > 0`. -/
theorem gauss_term_witness (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hk2 : 2 ≤ k) {β0 : ℝ} (hβ0 : 0 < β0) :
    ((betaK d L k β0 : ℝ) : ℂ) * ∑ z ∈ ({z0W d L N₁ m₁ k} : Finset _), (1 / 2 : ℂ) *
        (aNW d L N₁ m₁ k (hk1 hk2) z : ℂ) *
        dotC (kAvg (dataInc (winW d L N₁ m₁ k (hk1 hk2)) (DuW d L N₁ m₁ k (hk1 hk2))) z)
          (kAvg (dataInc (winW d L N₁ m₁ k (hk1 hk2)) (DuW d L N₁ m₁ k (hk1 hk2))) z) =
      ((betaK d L k β0 * aNW d L N₁ m₁ k (hk1 hk2) (z0W d L N₁ m₁ k) : ℝ) : ℂ) ∧
    0 < betaK d L k β0 * aNW d L N₁ m₁ k (hk1 hk2) (z0W d L N₁ m₁ k) := by
  have hpos : 0 < aNW d L N₁ m₁ k (hk1 hk2) (z0W d L N₁ m₁ k) :=
    compWeightZ_pos one_pos (by omega) _ (hZbW hk2 _ (Finset.mem_singleton_self _))
  have hb : 0 < betaK d L k β0 := by unfold betaK; positivity
  refine ⟨?_, mul_pos hb hpos⟩
  rw [Finset.sum_singleton, kAvg_inc_W hd3 hL (hk1 hk2), dot_vInc]
  push_cast
  ring

theorem aNW_pos (hk2 : 2 ≤ k) (hL : 3 ≤ L) : ∀ z ∈ ({z0W d L N₁ m₁ k} : Finset _),
    0 < aNW d L N₁ m₁ k (hk1 hk2) z := fun z hz =>
  compWeightZ_pos one_pos (by omega) _ (hZbW hk2 z hz)

/-- **`Cnat1_le` at the instance**: `|C^♮_1| ≤ ⅜ Σ_z β_k a^♮_z |Q_z δψ|²`. -/
theorem Cnat1_witness (hL : 3 ≤ L) (hk2 : 2 ≤ k) {β0 : ℝ} (hβ0 : 0 < β0) :
    ‖Cnat1 1 (precW (hk1 hk2)) (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) hW
        (DuW d L N₁ m₁ k (hk1 hk2)) {z0W d L N₁ m₁ k} β0 ϖW (aNW d L N₁ m₁ k (hk1 hk2))‖ ≤
      3 / 8 * ∑ z ∈ ({z0W d L N₁ m₁ k} : Finset _), betaK d L k β0 * aNW d L N₁ m₁ k (hk1 hk2) z *
        vn (kAvg (dataInc (winW d L N₁ m₁ k (hk1 hk2)) (DuW d L N₁ m₁ k (hk1 hk2))) z) ^ 2 :=
  Cnat1_le 1 (precW (hk1 hk2)) (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) hW
    (DuW d L N₁ m₁ k (hk1 hk2)) {z0W d L N₁ m₁ k} hβ0.le ϖW (aNW d L N₁ m₁ k (hk1 hk2))
    (fun z hz => (aNW_pos hk2 hL z hz).le)

theorem rBlk_witness (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hk : 1 ≤ k) (z : Torus d (N₁ * L ^ m₁ * L ^ (k - k)))
    (i : Fin 2) :
    rBlk (G d L N₁ m₁ k) (compWeight L 1) (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) hW z i =
      0 := by
  unfold rBlk
  rw [show phiZero (G d L N₁ m₁ k) (compWeight L 1) (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
      hW = unitPhi (G d L N₁ m₁ k) hN2' from phiZero_ψ0W hd3 hL hk]
  have : (fun y j => svec (G d L N₁ m₁ k) (unitPhi (G d L N₁ m₁ k) hN2') y j) =
      fun _ j => (unitVec hN2' j : ℂ) := funext fun y => funext fun j =>
    svec_unitPhi (isLevel_G hk) hN2' y j
  rw [this, kAvg_const_W]
  simp [ψ0W, eu]

theorem sBlk_witness (hk : 1 ≤ k) (z : Torus d (N₁ * L ^ m₁ * L ^ (k - k))) (i : Fin 2) :
    sBlk (Gw d L N₁ m₁ k hk) ϖW (DuW d L N₁ m₁ k hk).Ψ z i = 0 := by
  unfold sBlk ϖW
  simp

/-- **`Cnat0_le` at the instance** with its explicit constants `(36, 8, 9, 1)`: the parameters are
`η_k = 0` (since `a^♮_z = a_z`), `ρ = 0` (`r_z = 0`: the reference is the constant configuration), `σ = 0`
(`ϖ ≡ 1`), `n = 1 = #Z_b`. -/
theorem Cnat0_witness (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hk2 : 2 ≤ k) {β0 : ℝ} (hβ0 : 0 < β0) :
    ‖Cnat0 1 (precW (hk1 hk2)) (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) hW
        (DuW d L N₁ m₁ k (hk1 hk2)) {z0W d L N₁ m₁ k} β0 ϖW (aNW d L N₁ m₁ k (hk1 hk2))
        (ψkW d L N₁ m₁ k)‖ ≤
      1 * (36 * betaK d L k β0 * 0 * 0 ^ 2 + 8 * betaK d L k β0 * 0 * 0 + 9 * betaK d L k β0 * 0 ^ 2 +
        ((2 : ℕ) : ℝ) * 0) := by
  have hk := hk1 hk2
  have hZ := hZbW (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hk2
  have hadm := (H (k := k) hd3 hL).weights
  have hmem := fun z hz => compWeightZ_mem (a₁ := 1) hadm (G := Gw d L N₁ m₁ k hk) (hZ z hz)
  refine Cnat0_le (ηk := 0) (ρ := 0) (σ := 0) (n := 1) 1 (precW hk) (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) hW
    (by omega) hk hadm hβ0.le (DuW d L N₁ m₁ k hk) (DW d L N₁ m₁ k hk) {z0W d L N₁ m₁ k} ?_ hZ
    (fun x _ => G_layer hk x) (ψkW d L N₁ m₁ k) (fun _ _ _ => rfl) ϖW (aNW d L N₁ m₁ k hk)
    (fun z hz => (hmem z hz).1) (fun z hz => (hmem z hz).2) ?_ (by norm_num) le_rfl ?_ ?_ ?_ le_rfl le_rfl
  · intro z hz x hx
    unfold DW
    rw [regionOf_sites]
    exact Finset.mem_biUnion.2 ⟨z, hz, hx⟩
  · intro z hz
    have hne : compWeightZ (Gw d L N₁ m₁ k hk) 1 z ≠ 0 := (aNW_pos hk2 hL z hz).ne'
    show |compWeightZ (Gw d L N₁ m₁ k hk) 1 z / compWeightZ (Gw d L N₁ m₁ k hk) 1 z - 1| ≤ 0
    rw [div_self hne]; simp
  · intro z _
    have : rBlk (G d L N₁ m₁ k) (compWeight L 1) (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
        hW z = fun _ => 0 := funext fun i => rBlk_witness hd3 hL hk z i
    rw [this]; simp [vn]; rfl
  · intro z _
    have : sBlk (Gw d L N₁ m₁ k hk) ϖW (DuW d L N₁ m₁ k hk).Ψ z = fun _ => 0 :=
      funext fun i => sBlk_witness hk z i
    rw [this]; simp [vn]; rfl
  · simp

/-- At the instance `C^♮_0 = 0`. -/
theorem Cnat0_witness_eq_zero (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hk2 : 2 ≤ k) {β0 : ℝ}
    (hβ0 : 0 < β0) :
    Cnat0 1 (precW (hk1 hk2)) (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) hW
        (DuW d L N₁ m₁ k (hk1 hk2)) {z0W d L N₁ m₁ k} β0 ϖW (aNW d L N₁ m₁ k (hk1 hk2))
        (ψkW d L N₁ m₁ k) = 0 := by
  have := Cnat0_witness (m₁ := m₁) (N₁ := N₁) hd3 hL hk2 hβ0
  simp at this
  exact this

/-- The concrete instance `d = 3`, `L = 3`, `N₁ = 6`, `m₁ = 0`, `k = 2`. -/
theorem cancellation_identity_hyps_nonempty_concrete {β0 : ℝ} (ν : ℝ) (hβ0 : 0 < β0) :
    CancelIdentityStmt 3 3 6 0 2 (hk1 (le_refl 2)) β0 ν :=
  cancellation_identity_hyps_nonempty (by norm_num) (by norm_num) (by norm_num) le_rfl ν hβ0

end PsiZeroWitness
end Balaban.LargeField
