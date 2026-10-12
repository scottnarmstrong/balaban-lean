module

public import Balaban.LargeField.R.ChiBridgeHist
public import Balaban.LargeField.R.ZeroDomainB

/-!
# The geometric premise `hgeo` of the small factors (Part III, Lemma III.5.0)

`smallFactor_two_hist` and `smallFactor_five_hist` take the inclusion `hgeo` of Lemma III.5.0:
`□^{∼3} ⊂ Z^c_0 ∩ Z` for the `π_k`-cubes `□ ⊂ Z''^c_0 ∩ (Ω^c_k)^{∼3} ∩ Z` (item 2), and
`□^{∼3} ⊂ Z` for the `π_k`-cubes `□ ⊂ Z''_0 ∩ Z` (item 5).  Here these inclusions are proved for the
sets `Z_0` (`Zzero`) and `Z''_0` (`ZzeroDD`) of a component `Z` of the region history, with
`a = 𝔥_k(Z)` the localized history:

* `hgeo_five_fine`, `hgeo_two_fine`: the inclusions as statements on the sites of the history torus;
* `smallFactor_one_ripe`, `smallFactor_two_ripe`, `smallFactor_five_ripe`: the small-factor bounds
  with `a`, `Z_0`, `Z''_0` the sets of the component and `X_c = Z^c_0 ∩ Z`, `X = Z` given by their
  definition (as fine sets), without the premise `hgeo`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M]

/-- The fine set `Z_0`: the fine sites of the history torus lying in a `k`-block of `Z₀`. -/
def fineZzero (k : ℕ) (Z : H.Comp k) : Set (Torus S.d (S.M * n K * S.L ^ K)) :=
  {x | blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k Z}

include H in
theorem fineTorus_eq {k : ℕ} (hkK : k ≤ K) :
    S.M * n K * S.L ^ K = S.M * n k * S.L ^ k := by
  rw [(fine_eq (H.F.hnn) hkK : S.M * n K * S.L ^ K = S.L ^ k * S.M * n k)]
  ring

include H in
theorem cubeMap_torusCast {k j : ℕ} (hkK : k ≤ K) (x : Torus S.d (S.M * n K * S.L ^ K)) :
    cubeMap n S.L S.M k j (torusCast (H.fineTorus_eq hkK) x) = cubeMap n S.L S.M K j x := by
  unfold cubeMap
  rw [blockMap_torusCast]

/-- **Lemma III.5.0 (b), item 5**: the `π_k`-cubes `□ ⊂ Z''₀ ∩ Z` have `□^{∼3} ⊂ Z`. -/
theorem hgeo_five_fine (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) {k : ℕ} (hkK : k ≤ K) (hk : 1 ≤ k)
    (Z : H.Comp k) :
    ∀ y0 ∈ cubeFin (S := S) (chiZDDCubes (H.localHistory S.M K k Z) k
        (fineSet (S := S) (n := n) S.M K k (H.ZzeroDD k Z))),
      ∀ x : Torus S.d (S.M * n K * S.L ^ K),
        cubeMap n S.L S.M K k x ∈ nbhd 3 {y0} → cubeMap n S.L S.M K k x ∈ Z.1 := by
  intro y0 hy0 x hx
  have hy0' : CubeSub (S := S) (n := n) S.M K k y0
      (fineSet (S := S) (n := n) S.M K k (H.ZzeroDD k Z) ∩ (H.localHistory S.M K k Z).Z k) := by
    have h : y0 ∈ chiZDDCubes (H.localHistory S.M K k Z) k
        (fineSet (S := S) (n := n) S.M K k (H.ZzeroDD k Z)) := by simpa [cubeFin] using hy0
    exact h
  obtain ⟨x0, hx0⟩ := exists_site_of_cube (M := S.M) (K := K) H.F.hnn hkK y0
  have hZZ : y0 ∈ H.ZzeroDD k Z := by
    have := (hy0' x0 hx0).1
    simpa [fineSet, hx0] using this
  obtain ⟨y, hy, hd⟩ := mem_nbhd.mp hx
  rw [Set.mem_singleton_iff] at hy
  rw [hy] at hd
  have hxn : cubeMap n S.L S.M K k x ∈ nbhd 3 (H.ZzeroDD k Z) := mem_nbhd.mpr ⟨y0, hZZ, hd⟩
  have := H.ZzeroDD_nbhd_margin hR hkK hk Z (x := torusCast (H.fineTorus_eq hkK) x)
    (by rw [H.cubeMap_torusCast hkK]; exact hxn)
  have h3 := this.2.2
  rwa [H.cubeMap_torusCast hkK] at h3

/-- **Lemma III.5.0 (a), item 2**: the `π_k`-cubes `□ ⊂ Z''^c₀ ∩ (Ω^c_k)^{∼3} ∩ Z` have
`□^{∼3} ⊂ Z^c₀ ∩ Z`; `Z_0` is `fineZzero`, `Z''_0` is the fine set of `ZzeroDD`. -/
theorem hgeo_two_fine {k : ℕ} (hkK : k ≤ K) (hk : 1 ≤ k)
    (Z : H.Comp k) :
    ∀ y0 ∈ cubeFin (S := S) (chiSCubes (H.localHistory S.M K k Z) k
        (fineSet (S := S) (n := n) S.M K k (H.ZzeroDD k Z))),
      ∀ x : Torus S.d (S.M * n K * S.L ^ K),
        cubeMap n S.L S.M K k x ∈ nbhd 3 {y0} →
          cubeMap n S.L S.M K k x ∈ Z.1 ∧ x ∉ H.fineZzero k Z := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  intro y0 hy0 x hx
  have hy0' : y0 ∈ chiSCubes (H.localHistory S.M K (k' + 1) Z) (k' + 1)
      (fineSet (S := S) (n := n) S.M K (k' + 1) (H.ZzeroDD (k' + 1) Z)) := by
    simpa [cubeFin] using hy0
  obtain ⟨x0, hx0⟩ := exists_site_of_cube (M := S.M) (K := K) H.F.hnn hkK y0
  have hx0t := hy0' x0 hx0
  obtain ⟨⟨-, hx0Z0⟩, hx0Ω⟩ := hx0t
  have hyZ : y0 ∉ H.ZzeroDD (k' + 1) Z := by
    intro h; apply hx0Z0; show cubeMap n S.L S.M K (k' + 1) x0 ∈ H.ZzeroDD (k' + 1) Z; rw [hx0]; exact h
  have hx0Ω' : cubeMap n S.L S.M K (k' + 1) x0 ∈ omegaCNb (H.localHistory S.M K (k' + 1) Z) 3 (k' + 1) :=
    hx0Ω
  rw [hx0] at hx0Ω'
  obtain ⟨c', hc', hdc⟩ := mem_nbhd.mp hx0Ω'
  obtain ⟨s, hs⟩ := exists_site_of_cube (M := S.M) (K := K) H.F.hnn hkK c'
  obtain ⟨-, hsO⟩ := hc' s hs
  have hsZ : s ∈ fineSet (S := S) (n := n) S.M K (k' + 1) (Z.1 : Set (Torus S.d (n (k' + 1)))) :=
    (hc' s hs).1.2
  have hnO : c' ∉ ((H.locRH (k' + 1) Z).step k').Omega := by
    intro h
    apply hsO
    have h' : cubeMap n S.L S.M K (k' + 1) s ∈ ((H.locRH (k' + 1) Z).step k').Omega := by
      rw [hs]; exact h
    exact ⟨h', hsZ⟩
  obtain ⟨y1, hy1, hd⟩ := mem_nbhd.mp hx
  rw [Set.mem_singleton_iff] at hy1
  rw [hy1] at hd
  have h6 : supDist (cubeMap n S.L S.M K (k' + 1) x) c' ≤ 6 :=
    (supDist_triangle _ y0 c').trans (by omega)
  refine ⟨H.nbhd_six_Omega_compl_subset hkK Z hnO h6, ?_⟩
  intro hZ0
  have hS := H.F.ok
  have hsep := H.ZzeroDD_sep hS hkK (H.eight_le_L_mul_lateR (k' + 1)) Z hyZ hZ0
  apply hsep
  have e : blockMap S.M (n (k' + 1)) (blockMap (S.L ^ (k' + 1)) (S.M * n (k' + 1)) x) =
      cubeMap n S.L S.M K (k' + 1) x := by
    unfold cubeMap
    rw [blockMap_comp (by
      rw [(fine_eq (H.F.hnn) hkK : S.M * n K * S.L ^ K = S.L ^ (k' + 1) * S.M * n (k' + 1))]
      ring) rfl]
  rw [e]
  exact mem_nbhd.mpr ⟨y0, rfl, hd⟩

/-- A site of the level torus and its image in the history torus have the same `π_k`-cube. -/
theorem blockMap_level_eq_cubeMap (g : Geo S n R S.M) {k : ℕ} (hkK : k ≤ K)
    (x : Site S.d S.L (g.M1 * (g.c * n k)) k) :
    blockMap (S.L ^ k * (g.c * g.M1)) (n k) x =
      cubeMap n S.L S.M K k (torusCast (histFine_eq g H.F.hnn hkK) x) := by
  unfold cubeMap
  rw [blockMap_torusCast, ← g.hM]

end RegionHistory

section Ripe

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  [NeZero S.L] [NeZero S.M] {Nspin : ℕ} {ϱ : ℝ} {k : ℕ}

/-- **Lemma III.5.3 (a), `ϰ₁`, for a component `Z`** (premise-free form of `smallFactor_one_hist`):
`a = 𝔥_k(Z)` is the localized history of `Z`, `Z_0` is `fineZzero`, and the fine set `Xc = Z^c_0 ∩ Z`
is given by its definition. -/
theorem smallFactor_one_ripe (P : SmallFactorPar) (H : RegionHistory S n R k0 K)
    (g : Geo S n R S.M) (hkK : k ≤ K) (Z : H.Comp k)
    (G : GeneratingSet S.d S.L (g.M1 * (g.c * n k)) k ϱ) (hk : 1 ≤ k)
    (hL : 2 ≤ S.L) (hd : 2 ≤ S.d) (hϱ : 2 * (S.d : ℝ) * S.L ≤ ϱ) {a₁ : ℝ} (ha₁ : 0 < a₁)
    (hadm : IsAdmissibleWeights k (compWeight S.L a₁)) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) {Xc Xwin : Finset (Site S.d S.L (g.M1 * (g.c * n k)) k)}
    (hXcdef : ∀ x, x ∈ Xc ↔
      torusCast (histFine_eq g H.F.hnn hkK) x ∈ fineSet (S := S) (n := n) S.M K k (Z.1 : Set _) ∧
      torusCast (histFine_eq g H.F.hnn hkK) x ∉ H.fineZzero k Z)
    (hXc : Xc ⊆ Xwin) (hXΩ : ∀ s ∈ Xc, s ∈ G.Ω 1 ∧ s ∉ G.Ω k)
    (hXk : IsBlockUnion S.L (g.M1 * (g.c * n k)) k k Xc)
    (hX : ∀ m, 1 ≤ m → m ≤ k → IsBlockUnion S.L (g.M1 * (g.c * n k)) k m (Xc ∩ G.layer m))
    (ψ : (m : ℕ) → Blk S.d S.L (g.M1 * (g.c * n k)) k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site S.d S.L (g.M1 * (g.c * n k)) k → EuclideanSpace ℝ (Fin Nspin))
    (hφ : ∀ x ∈ Xc, ‖φ x‖ = 1) {βk : ℝ} (hβ : 0 ≤ βk) (ϖ : ℕ → ℝ)
    (aN : Blk S.d S.L (g.M1 * (g.c * n k)) k k → ℝ) (hη0 : 0 ≤ P.eta) (hη : P.eta ≤ 1 / 2)
    (haN : ∀ z ∈ tBlocks S.d S.L (g.M1 * (g.c * n k)) k k Xc,
      |aN z - compWeightZ G a₁ z| ≤ P.eta * compWeightZ G a₁ z)
    {Mψ Sig Nbl : ℝ} (hM : ∀ s ∈ Xc, ‖leafField G ψ s‖ ≤ Mψ)
    (hSig : ∀ z ∈ tBlocks S.d S.L (g.M1 * (g.c * n k)) k k Xc,
      Real.sqrt βk * varsigmaBar G ϖ z ≤ Sig)
    (hN : ((tBlocks S.d S.L (g.M1 * (g.c * n k)) k k Xc).card : ℝ) ≤ Nbl)
    (hΛ19 : 8 * Sig ^ 2 * Nbl * Mψ ^ 2 ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ) (hγ0 : P.gamma0 = gamma0 S.d)
    (hβδ : βk * δ ^ 2 = P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a)
    (ψh : BlockAt S n S.M K k → EuclideanSpace ℝ (Fin Nspin))
    (hψk : ∀ z, ψ k z = ψh (torusCast (histScale_eq g.hM H.F.hnn (le_refl k) hkK) z))
    (hχ : chiTilde (H.localHistory S.M K k Z) k (H.fineZzero k Z) δ ψh = 0) :
    P.gamma1 ≤ 1 / 2 * composedGauss G βk aN ϖ ψ Xc +
      multiAction G (compWeight S.L a₁) βk μ h Xwin ψ φ := by
  refine smallFactor_one_hist P g H.F.hnn hkK G hk hL hd hϱ ha₁ hadm hμ h hXc hXΩ hXk hX ψ φ hφ hβ ϖ aN
    hη0 hη haN hM hSig hN hΛ19 hδ hγ0 hβδ (H.localHistory S.M K k Z) (H.fineZzero k Z) ψh hψk ?_ hχ
  intro x hx
  rw [hXcdef, torusCast_cast_symm]
  exact ⟨hx.1.1.2, hx.1.2⟩

/-- **Lemma III.5.3 (b), `ϰ₂`, for a component `Z`** (premise-free form of `smallFactor_two_hist`):
the premise `hgeo` (Lemma III.5.0 (a)) is proved (`hgeo_two_fine`); `a = 𝔥_k(Z)`, `Z_0 = fineZzero`,
`Z''_0` = the fine set of `ZzeroDD`, and `Xc = Z^c_0 ∩ Z` is given by its definition. -/
theorem smallFactor_two_ripe (P : SmallFactorPar) (H : RegionHistory S n R k0 K)
    (g : Geo S n R S.M) (hkK : k ≤ K) (Z : H.Comp k) (cs : OpConsts)
    (G : GeneratingSet S.d S.L (g.M1 * (g.c * n k)) k ϱ) (hk : 1 ≤ k)
    (hL : 2 ≤ S.L) (hd : 2 ≤ S.d) (hϱ : 2 * (S.d : ℝ) * S.L ≤ ϱ) {a₁ : ℝ} (ha₁ : 0 < a₁)
    (hadm : IsAdmissibleWeights k (compWeight S.L a₁)) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) {Xc Xwin : Finset (Site S.d S.L (g.M1 * (g.c * n k)) k)}
    (hXcdef : ∀ x, x ∈ Xc ↔
      torusCast (histFine_eq g H.F.hnn hkK) x ∈ fineSet (S := S) (n := n) S.M K k (Z.1 : Set _) ∧
      torusCast (histFine_eq g H.F.hnn hkK) x ∉ H.fineZzero k Z)
    (hXc : Xc ⊆ Xwin) (hXΩ : ∀ s ∈ Xc, s ∈ G.Ω 1 ∧ s ∉ G.Ω k)
    (hXk : IsBlockUnion S.L (g.M1 * (g.c * n k)) k k Xc)
    (hX : ∀ m, 1 ≤ m → m ≤ k → IsBlockUnion S.L (g.M1 * (g.c * n k)) k m (Xc ∩ G.layer m))
    (ψ : (m : ℕ) → Blk S.d S.L (g.M1 * (g.c * n k)) k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site S.d S.L (g.M1 * (g.c * n k)) k → EuclideanSpace ℝ (Fin Nspin))
    (hφ : ∀ x ∈ Xc, ‖φ x‖ = 1) {βk : ℝ} (hβ : 0 ≤ βk) (ϖ : ℕ → ℝ)
    (aN : Blk S.d S.L (g.M1 * (g.c * n k)) k k → ℝ) (hη0 : 0 ≤ P.eta) (hη : P.eta ≤ 1 / 2)
    (haN : ∀ z ∈ tBlocks S.d S.L (g.M1 * (g.c * n k)) k k Xc,
      |aN z - compWeightZ G a₁ z| ≤ P.eta * compWeightZ G a₁ z)
    {Mψ Sig Nbl : ℝ} (hM : ∀ s ∈ Xc, ‖leafField G ψ s‖ ≤ Mψ)
    (hSig : ∀ z ∈ tBlocks S.d S.L (g.M1 * (g.c * n k)) k k Xc,
      Real.sqrt βk * varsigmaBar G ϖ z ≤ Sig)
    (hN : ((tBlocks S.d S.L (g.M1 * (g.c * n k)) k k Xc).card : ℝ) ≤ Nbl)
    (hΛ19 : 8 * Sig ^ 2 * Nbl * Mψ ^ 2 ≤ 1) (hδ : 0 < cs.delta k) (hK1 : 0 < P.K1)
    (hγ0 : P.gamma0 = gamma0 S.d)
    (hβδ : βk * (cs.delta k) ^ 2 = P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a)
    (hK1b : bgK1 S.d S.L Nspin ≤ P.K1) (hδ1 : cs.delta k ≤ 6 * P.K1)
    (hδc : cs.delta k ≤ 2 * P.K1 * bgC1 S.d S.L Nspin)
    (hmu : cs.mu k = 0) (Hbg : BgHyp S.d S.L k (minSep S.L g.M1) cs.aw 0)
    (ψh : BlockAt S n S.M K k → EuclideanSpace ℝ (Fin Nspin))
    (hψk : ∀ z, ψ k z = ψh (torusCast (histScale_eq g.hM H.F.hnn (le_refl k) hkK) z))
    (hχ : chiS (H.localHistory S.M K k Z) k g H.F.hnn cs h hkK
      (fineSet (S := S) (n := n) S.M K k (H.ZzeroDD k Z)) ψh = 0) :
    P.gamma2 ≤ composedGauss G βk aN ϖ ψ Xc +
      multiAction G (compWeight S.L a₁) βk μ h Xwin ψ φ := by
  refine smallFactor_two_hist P g H.F.hnn hkK cs G hk hL hd hϱ ha₁ hadm hμ h hXc hXΩ hXk hX ψ φ hφ hβ
    ϖ aN hη0 hη haN hM hSig hN hΛ19 hδ hK1 hγ0 hβδ hK1b hδ1 hδc hmu Hbg (H.localHistory S.M K k Z)
    (fineSet (S := S) (n := n) S.M K k (H.ZzeroDD k Z)) ψh hψk ?_ hχ
  intro y0 hy0 x hx
  rw [H.blockMap_level_eq_cubeMap g hkK] at hx
  have := H.hgeo_two_fine hkK hk Z y0 hy0 _ hx
  rw [hXcdef]
  exact this

/-- **Lemma III.5.3 (e), `ϰ₅`, for a component `Z`** (premise-free form of `smallFactor_five_hist`):
the premise `hgeo` (Lemma III.5.0 (b)) is proved (`hgeo_five_fine`), under the operative radii
`R_j = R_base λ̂_j²` (version 1.2, D-IV.2); `X = Z` is given by its definition as a fine set. -/
theorem smallFactor_five_ripe (P : SmallFactorPar) (H : RegionHistory S n R k0 K)
    (hR : ∀ j, R j = S.Rb * S.lam j ^ 2)
    (g : Geo S n R S.M) (hkK : k ≤ K) (Z : H.Comp k) (cs : OpConsts)
    (hk : 1 ≤ k) (hd : 2 ≤ S.d) (hL : 2 ≤ S.L)
    (hϱ : 2 * (S.d : ℝ) * S.L ≤ ϱ) {μ : ℝ}
    (hμ : 0 ≤ μ) (h : EuclideanSpace ℝ (Fin Nspin))
    {X : Finset (Site S.d S.L (g.M1 * (g.c * n k)) k)}
    (hXdef : ∀ x, x ∈ X ↔
      torusCast (histFine_eq g H.F.hnn hkK) x ∈ fineSet (S := S) (n := n) S.M K k (Z.1 : Set _))
    (hXk : IsBlockUnion S.L (g.M1 * (g.c * n k)) k k X)
    (ψ : (m : ℕ) → Blk S.d S.L (g.M1 * (g.c * n k)) k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site S.d S.L (g.M1 * (g.c * n k)) k → EuclideanSpace ℝ (Fin Nspin))
    (hφ : ∀ x ∈ X, ‖φ x‖ = 1) {βk : ℝ} (hβ : 0 ≤ βk) (hδ : 0 < cs.delta k) (hK1 : 0 < P.K1)
    (hγ0 : P.gamma0 = gamma0 S.d)
    (hβδ : βk * (cs.delta k) ^ 2 = P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a)
    (hK1b : bgK1 S.d S.L Nspin ≤ P.K1) (hδ1 : cs.delta k ≤ 6 * P.K1)
    (hδc : cs.delta k ≤ 2 * P.K1 * bgC1 S.d S.L Nspin)
    (hmu : cs.mu k = 0) (Hbg : BgHyp S.d S.L k (minSep S.L g.M1) cs.aw 0)
    (ψh : BlockAt S n S.M K k → EuclideanSpace ℝ (Fin Nspin))
    (hψk : ∀ z, ψ k z = ψh (torusCast (histScale_eq g.hM H.F.hnn (le_refl k) hkK) z))
    (hχ : chiZDD (H.localHistory S.M K k Z) k g H.F.hnn cs h hkK
      (fineSet (S := S) (n := n) S.M K k (H.ZzeroDD k Z)) ψh = 0) :
    P.gamma5 ≤ multiAction (singleGen S.d S.L (g.M1 * (g.c * n k)) k ϱ) cs.aw βk μ h X ψ φ := by
  refine smallFactor_five_hist P g H.F.hnn hkK cs hk hd hL hϱ hμ h hXk ψ φ hφ hβ hδ hK1 hγ0 hβδ hK1b
    hδ1 hδc hmu Hbg (H.localHistory S.M K k Z)
    (fineSet (S := S) (n := n) S.M K k (H.ZzeroDD k Z)) ψh hψk ?_ hχ
  intro y0 hy0 x hx
  rw [H.blockMap_level_eq_cubeMap g hkK] at hx
  have := H.hgeo_five_fine hR hkK hk Z y0 hy0 _ hx
  rw [hXdef]
  exact this

end Ripe

end Balaban.LargeField
