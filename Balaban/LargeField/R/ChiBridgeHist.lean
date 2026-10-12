module

public import Balaban.LargeField.R.ChiBridge
public import Balaban.LargeField.R.SmallFactorChi
public import Balaban.LargeField.Characteristic.Analytic
public import Balaban.LargeField.Operators.QuietIndep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Transport of the small factors to the history torus (Part III, Lemma III.5.3)

The functions `χ̃_k`, `χ_S`, `χ_{Z''}` of Definition III.5.1 are functions of the block field
`ψ_k` of the *history* torus (`BlockAt`), while the single-scale lower bounds
(`smallFactor_one_gamma1`, `smallFactor_two`, `smallFactor_five`) are statements about the
level-`k` torus `Torus d (M₁ (c n_k) L^k)`.  The two are the same set of blocks
(`histScale_eq`); the identification is `torusCast`.

* `torusCast_*`, `jBlock_torusCast`: `torusCast` commutes with the block maps;
* `psiTildeSet_of_cast`: transport of `Ψ̃(T; δ)` along a torus-size equality;
* `smallFactor_one_hist`, `smallFactor_two_hist`, `smallFactor_five_hist`: the small factors for
  `χ̃_k = 0`, `χ_S = 0`, `χ_{Z''} = 0` stated for the history block field `ψ_k`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory

section Cast

theorem torusCast_rfl {d m : ℕ} (y : Torus d m) : torusCast rfl y = y := rfl

theorem torusCast_symm_cast {d m m' : ℕ} (h : m = m') (y : Torus d m) :
    torusCast h.symm (torusCast h y) = y := by
  subst h; rfl

theorem torusCast_cast_symm {d m m' : ℕ} (h : m = m') (y : Torus d m') :
    torusCast h (torusCast h.symm y) = y := by
  subst h; rfl

theorem torusCast_injective {d m m' : ℕ} (h : m = m') :
    Function.Injective (torusCast (d := d) h) := by
  intro x y hxy
  have := congrArg (torusCast h.symm) hxy
  rwa [torusCast_symm_cast, torusCast_symm_cast] at this

/-- Transport of `Ψ̃(T; δ)` along an equality of torus sizes: if `f = f' ∘ cast` and every point of
`T'` is the image of a point of `T`, then `Ψ̃(T; δ)` for `f` implies `Ψ̃(T'; δ)` for `f'`. -/
theorem psiTildeSet_of_cast {d m m' Nspin : ℕ} (h : m = m') (T : Set (Torus d m))
    (T' : Set (Torus d m')) (f : Torus d m → EuclideanSpace ℝ (Fin Nspin))
    (f' : Torus d m' → EuclideanSpace ℝ (Fin Nspin)) (hf : ∀ y, f y = f' (torusCast h y))
    (hT : ∀ y' ∈ T', ∃ y ∈ T, torusCast h y = y') {δ : ℝ} (hP : PsiTildeSet T f δ) :
    PsiTildeSet T' f' δ := by
  subst h
  refine ⟨fun y hy y' hy' hadj => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := hT y hy
    obtain ⟨z', hz', rfl⟩ := hT y' hy'
    have := hP.1 z hz z' hz' hadj
    rwa [hf, hf] at this
  · obtain ⟨z, hz, rfl⟩ := hT y hy
    have := hP.2 z hz
    rwa [hf] at this

end Cast

section JBlock

variable {d L : ℕ} [NeZero L]

/-- `torusCast` commutes with the block map: the `j`-block of a site of the level torus
`Torus d (N₀ L^k)` and of the same site in `Torus d (N₀' L^K)` (`N₀ L^k = N₀' L^K`) correspond. -/
theorem jBlock_torusCast {N₀ N₀' k K j : ℕ} [NeZero N₀] [NeZero N₀'] (hjk : j ≤ k) (hjK : j ≤ K)
    (hfine : N₀ * L ^ k = N₀' * L ^ K) (hblk : N₀ * L ^ (k - j) = N₀' * L ^ (K - j))
    (x : Torus d (N₀ * L ^ k)) :
    jBlock d L N₀' K j (torusCast hfine x) = torusCast hblk (jBlock d L N₀ k j x) := by
  funext i
  apply ZMod.val_injective
  rw [torusCast_val]
  have h1 : (jBlock d L N₀' K j (torusCast hfine x) i).val =
      ((torusCast hfine x) i).val / L ^ j := by
    unfold jBlock
    exact blockCoord_val (side_eq hjK) _
  have h2 : (jBlock d L N₀ k j x i).val = (x i).val / L ^ j := by
    unfold jBlock
    exact blockCoord_val (side_eq hjk) _
  rw [h1, h2, torusCast_val]

end JBlock

section Hist

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- The fine tori agree: `M₁ (c n_k) L^k = M n_K L^K`. -/
theorem histFine_eq (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K) :
    g.M1 * (g.c * n k) * S.L ^ k = M * n K * S.L ^ K := by
  have := histScale_eq g.hM hnn (i := 0) (q := k) (Nat.zero_le k) hkK
  simpa using this

end Hist

section SmallFactorsHist

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {Nspin : ℕ} {ϱ : ℝ} {k : ℕ}

/-- **Lemma III.5.3 (a), `ϰ₁`, on the history torus** (`torusCast` transport of
`smallFactor_one_gamma1`): if `χ̃_k(ψ_k) = 0` for the history block field `ψ_k`, i.e.
`ψ_k ∉ Ψ̃_k(Z^c_0 ∩ (Ω^c_k)^{∼3}; 3δ_k)`, and the fine set `Xc = Z^c_0 ∩ Z` of the level-`k` torus
contains that region, then `½ 𝒢^♮ + β_kA^*_k(X_win, 𝔹_k; ψ, φ) ≥ γ₁`.  `hψk` identifies the level
field with the history field. -/
theorem smallFactor_one_hist (P : SmallFactorPar) (g : Geo S n R M)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hkK : k ≤ K)
    (G : GeneratingSet S.d S.L (g.M1 * (g.c * n k)) k ϱ) (hk : 1 ≤ k)
    (hL : 2 ≤ S.L) (hd : 2 ≤ S.d) (hϱ : 2 * (S.d : ℝ) * S.L ≤ ϱ) {a₁ : ℝ} (ha₁ : 0 < a₁)
    (hadm : IsAdmissibleWeights k (compWeight S.L a₁)) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) {Xc Xwin : Finset (Site S.d S.L (g.M1 * (g.c * n k)) k)}
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
    (a : LocalHistory S n M K) (Z0 : Set (Torus S.d (M * n K * S.L ^ K)))
    (ψh : BlockAt S n M K k → EuclideanSpace ℝ (Fin Nspin))
    (hψk : ∀ z, ψ k z = ψh (torusCast (histScale_eq g.hM hnn (le_refl k) hkK) z))
    (hreg : ∀ x ∈ tildeRegion a k Z0, torusCast (histFine_eq g hnn hkK).symm x ∈ Xc)
    (hχ : chiTilde a k Z0 δ ψh = 0) :
    P.gamma1 ≤ 1 / 2 * composedGauss G βk aN ϖ ψ Xc +
      multiAction G (compWeight S.L a₁) βk μ h Xwin ψ φ := by
  have hnot : ¬ ChiTildeProp a k Z0 δ ψh := fun hc => by
    have := charFn_eq_one hc
    unfold chiTilde at hχ
    rw [this] at hχ
    exact one_ne_zero hχ
  have hviol : ¬ PsiTildeSet {y : Blk S.d S.L (g.M1 * (g.c * n k)) k k |
      fib S.d S.L (g.M1 * (g.c * n k)) k k y ⊆ Xc} (ψ k) (3 * δ) := by
    intro hP
    refine hnot (psiTildeSet_of_cast (histScale_eq g.hM hnn (le_refl k) hkK) _ _ (ψ k) ψh hψk
      ?_ hP)
    intro yh hyh
    refine ⟨torusCast (histScale_eq g.hM hnn (le_refl k) hkK).symm yh, ?_,
      torusCast_cast_symm _ _⟩
    intro xl hxl
    have hxl' : blkMap S.d S.L (g.M1 * (g.c * n k)) k k xl =
        torusCast (histScale_eq g.hM hnn (le_refl k) hkK).symm yh := (Finset.mem_filter.1 hxl).2
    have hj := jBlock_torusCast (L := S.L) (N₀ := g.M1 * (g.c * n k)) (N₀' := M * n K)
      (k := k) (K := K) (j := k) le_rfl hkK (histFine_eq g hnn hkK)
      (histScale_eq g.hM hnn (le_refl k) hkK) xl
    have hx : jBlock S.d S.L (M * n K) K k (torusCast (histFine_eq g hnn hkK) xl) = yh := by
      rw [hj]
      have : jBlock S.d S.L (g.M1 * (g.c * n k)) k k xl =
          torusCast (histScale_eq g.hM hnn (le_refl k) hkK).symm yh := hxl'
      rw [this, torusCast_cast_symm]
    have := hreg _ (hyh _ hx)
    rwa [torusCast_symm_cast] at this
  exact smallFactor_one_gamma1 P G hk hL hd hϱ ha₁ hadm hμ h hXc hXΩ hXk hX ψ φ hφ hβ ϖ aN hη0 hη
    haN hM hSig hN hΛ19 hδ hγ0 hβδ hviol

/-- **Lemma III.5.3 (b), `ϰ₂`, on the history torus**: if `χ_S(ψ_k) = 0` (`χ_S = ∏ χ_k(□)` over the
`π_k`-cubes `□ ⊂ Z''^c_0 ∩ (Ω^c_k)^{∼3} ∩ Z`, with `δ_k = cs.delta k` and the massless `μ_k = 0`)
and `□^{∼3} ⊂ Xc = Z^c_0 ∩ Z` as fine sets for those cubes (Lemma III.5.0 (a): `□^{∼3} ∩ Z_0 = ∅`,
and `□^{∼3} ⊂ Z`; the hypothesis `hgeo`), then `𝒢^♮ + β_kA^*_k(X_win, 𝔹_k; ψ, φ) ≥ γ₂`. -/
theorem smallFactor_two_hist (P : SmallFactorPar) (g : Geo S n R M)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hkK : k ≤ K) (cs : OpConsts)
    (G : GeneratingSet S.d S.L (g.M1 * (g.c * n k)) k ϱ) (hk : 1 ≤ k)
    (hL : 2 ≤ S.L) (hd : 2 ≤ S.d) (hϱ : 2 * (S.d : ℝ) * S.L ≤ ϱ) {a₁ : ℝ} (ha₁ : 0 < a₁)
    (hadm : IsAdmissibleWeights k (compWeight S.L a₁)) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) {Xc Xwin : Finset (Site S.d S.L (g.M1 * (g.c * n k)) k)}
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
    (hmu : cs.mu k = 0) (H : BgHyp S.d S.L k (minSep S.L g.M1) cs.aw 0)
    (a : LocalHistory S n M K) (Z0DD : Set (Torus S.d (M * n K * S.L ^ K)))
    (ψh : BlockAt S n M K k → EuclideanSpace ℝ (Fin Nspin))
    (hψk : ∀ z, ψ k z = ψh (torusCast (histScale_eq g.hM hnn (le_refl k) hkK) z))
    (hgeo : ∀ y0 ∈ cubeFin (S := S) (chiSCubes a k Z0DD),
      ∀ x : Site S.d S.L (g.M1 * (g.c * n k)) k,
        blockMap (S.L ^ k * (g.c * g.M1)) (n k) x ∈ nbhd 3 {y0} → x ∈ Xc)
    (hχ : chiS a k g hnn cs h hkK Z0DD ψh = 0) :
    P.gamma2 ≤ composedGauss G βk aN ϖ ψ Xc +
      multiAction G (compWeight S.L a₁) βk μ h Xwin ψ φ := by
  refine smallFactor_two (c := g.c) (n := n k) P G hk hL hd hϱ ha₁ hadm hμ h hXc hXΩ hXk hX ψ φ
    hφ hβ ϖ aN hη0 hη haN hM hSig hN hΛ19 hδ hK1 hγ0 hβδ hK1b hδ1 hδc H (by simp)
    (cubeFin (S := S) (chiSCubes a k Z0DD)) (g.hc.trans' (by norm_num)) hgeo ?_
  have e : (fun z i => ψ k z i) = blockCfgOf g hnn le_rfl hkK ψh := by
    funext z i; rw [hψk]; rfl
  rw [e]
  unfold chiS chiProd at hχ
  rw [hmu] at hχ
  exact hχ

/-- **Lemma III.5.3 (e), `ϰ₅`, on the history torus**: if `χ_{Z''}(ψ_k) = 0`
(`∏ χ_k(□)` over the `π_k`-cubes `□ ⊂ Z''_0 ∩ Z`) and `□^{∼3} ⊂ X = Z` as fine sets for those cubes
(`(Z''_0)^{∼3} ⊂ Z`, Lemma III.5.0 (b); the hypothesis `hgeo`), then `β_kA^*_k(Z; ψ_k, φ) ≥ γ₅`. -/
theorem smallFactor_five_hist (P : SmallFactorPar) (g : Geo S n R M)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hkK : k ≤ K) (cs : OpConsts)
    (hk : 1 ≤ k) (hd : 2 ≤ S.d) (hL : 2 ≤ S.L)
    (hϱ : 2 * (S.d : ℝ) * S.L ≤ ϱ) {μ : ℝ}
    (hμ : 0 ≤ μ) (h : EuclideanSpace ℝ (Fin Nspin))
    {X : Finset (Site S.d S.L (g.M1 * (g.c * n k)) k)}
    (hXk : IsBlockUnion S.L (g.M1 * (g.c * n k)) k k X)
    (ψ : (m : ℕ) → Blk S.d S.L (g.M1 * (g.c * n k)) k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site S.d S.L (g.M1 * (g.c * n k)) k → EuclideanSpace ℝ (Fin Nspin))
    (hφ : ∀ x ∈ X, ‖φ x‖ = 1) {βk : ℝ} (hβ : 0 ≤ βk) (hδ : 0 < cs.delta k) (hK1 : 0 < P.K1)
    (hγ0 : P.gamma0 = gamma0 S.d)
    (hβδ : βk * (cs.delta k) ^ 2 = P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a)
    (hK1b : bgK1 S.d S.L Nspin ≤ P.K1) (hδ1 : cs.delta k ≤ 6 * P.K1)
    (hδc : cs.delta k ≤ 2 * P.K1 * bgC1 S.d S.L Nspin)
    (hmu : cs.mu k = 0) (H : BgHyp S.d S.L k (minSep S.L g.M1) cs.aw 0)
    (a : LocalHistory S n M K) (Z0DD : Set (Torus S.d (M * n K * S.L ^ K)))
    (ψh : BlockAt S n M K k → EuclideanSpace ℝ (Fin Nspin))
    (hψk : ∀ z, ψ k z = ψh (torusCast (histScale_eq g.hM hnn (le_refl k) hkK) z))
    (hgeo : ∀ y0 ∈ cubeFin (S := S) (chiZDDCubes a k Z0DD),
      ∀ x : Site S.d S.L (g.M1 * (g.c * n k)) k,
        blockMap (S.L ^ k * (g.c * g.M1)) (n k) x ∈ nbhd 3 {y0} → x ∈ X)
    (hχ : chiZDD a k g hnn cs h hkK Z0DD ψh = 0) :
    P.gamma5 ≤ multiAction (singleGen S.d S.L (g.M1 * (g.c * n k)) k ϱ) cs.aw βk μ h X ψ φ := by
  refine smallFactor_five (c := g.c) (n := n k) P hk hd hL hϱ H.weights hμ h hXk ψ φ hφ hβ hδ hK1 hγ0
    hβδ hK1b hδ1 hδc H (by simp) (cubeFin (S := S) (chiZDDCubes a k Z0DD))
    (g.hc.trans' (by norm_num)) hgeo ?_
  have e : (fun z i => ψ k z i) = blockCfgOf g hnn le_rfl hkK ψh := by
    funext z i; rw [hψk]; rfl
  rw [e]
  unfold chiZDD chiProd at hχ
  rw [hmu] at hχ
  exact hχ

end SmallFactorsHist

end Balaban.LargeField
