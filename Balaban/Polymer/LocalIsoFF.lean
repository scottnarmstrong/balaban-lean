/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalIsoDet
public import Balaban.Polymer.LocalIsoStrict
public import Balaban.Fluctuation.NewLevelTermsBgAnalytic
import Mathlib.Tactic.Linarith

/-!
# Local generating sets on two tori: the marked functional of the recomputed terms

The terms `evDecBg` of the step's expansion recomputed on a local generating set `Gb` with the
canonical transport read the marked functional `FFmarkedBg`: the decoupled background `F₁` of `Gb`
at the transported parameters, the decoupled fluctuation `Sol` of the pair `(coverOf Gb, Hm)` at
the data `flEdat …` of the masked local hat field, and a functional `Φ` of these.  For `Gb`, `Hm`
carried by the box map onto `Gb'`, `Hm'` (`OmegaIso`), all of these correspond:

* `OmegaIso.canon_par_eq`: the transported parameters (from the correspondence of the step's
  extended parameters at the top cubes of `Gb`);
* `OmegaIso.decCovSqrt_submatrix`, `OmegaIso.hatSqrtF_submatrix`: the decoupled square root at
  corresponding backgrounds;
* `OmegaIso.liftZ_eq`, `OmegaIso.markedHatPsiFBg_corr`: the masked local hat field corresponds on
  the box of radius `ρ + 1`;
* `OmegaIso.flEdat_corr`: the data of the fluctuation problem;
* `OmegaIso.FFmarkedBg_canon_eq`: **the marked functional at corresponding points**, from the
  values of the decoupling pairs (`decBg_value_eq`, `decSol_value_eq`) and the correspondence of
  `Φ` on corresponding inputs (`hΦ`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Polymer
  Balaban.Polymer.TwoTorusStep Balaban.Fluctuation Balaban.SmallField Matrix MeasureTheory

/-- The product of corresponding matrix and vector, for any equivalence of the indices. -/
theorem mulVec_corr_gen {ι ι' : Type*} [Fintype ι] [Fintype ι'] (f : ι ≃ ι')
    {M : Matrix ι ι ℂ} {M' : Matrix ι' ι' ℂ} (hM : ∀ a b, M' (f a) (f b) = M a b)
    {v : ι → ℂ} {v' : ι' → ℂ} (hv : ∀ b, v' (f b) = v b) (a : ι) :
    (M' *ᵥ v') (f a) = (M *ᵥ v) a := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← f.sum_comp]
  exact Finset.sum_congr rfl fun b _ => by rw [hM, hv]

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱ' ϱb ϱb' ϱm ϱm' : ℝ}

local notation "bk" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
local notation "ck" => (Prod.map id bk : ℕ × CTorus d L N₁ m₁ (k + 1) → ℕ × CTorus d L N₁' m₁ (k + 1))

namespace OmegaIso

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gp' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ'}
  {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Gb' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱb'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'} {ρ : ℕ}

/-- **The transported parameters** of the canonical transport at corresponding centres of `Gb`,
when the step's extended parameters correspond at the top cubes of `Gb`. -/
theorem canon_par_eq (hI : OmegaIso Gb Gb' ρ) {S : DecParams Gp} {S' : DecParams Gp'}
    (hS : ∀ P ∈ cubeIdx Gb, P.2 ∈ Gb.Ω (k + 1) →
      Dec2.extS (coverOf Gp') S' (ck P) = Dec2.extS (coverOf Gp) S P)
    (q : cubeIdx Gb) :
    (BgTransport.canon Gp' Gb' N).par S' (hI.cubeEquiv q) =
      (BgTransport.canon Gp Gb N).par S q := by
  have hq := hI.base_inBox q.2
  have hmem : (ck (q : ℕ × CTorus d L N₁ m₁ (k + 1))).2 ∈ Gb'.Ω (k + 1) ↔
      (q : ℕ × CTorus d L N₁ m₁ (k + 1)).2 ∈ Gb.Ω (k + 1) :=
    hI.corr _ (inBox_mono (Nat.le_succ ρ) hq) (k + 1) (by omega) le_rfl
  show (if (ck (q : ℕ × CTorus d L N₁ m₁ (k + 1))).2 ∈ Gb'.Ω (k + 1) then
      Dec2.extS (coverOf Gp') S' (ck q) else 0) =
    (if (q : ℕ × CTorus d L N₁ m₁ (k + 1)).2 ∈ Gb.Ω (k + 1) then
      Dec2.extS (coverOf Gp) S q else 0)
  by_cases h : (q : ℕ × CTorus d L N₁ m₁ (k + 1)).2 ∈ Gb.Ω (k + 1)
  · simp only [hmem.2 h, h, ↓reduceIte]
    exact hS q q.2 h
  · have h' : ¬ (ck (q : ℕ × CTorus d L N₁ m₁ (k + 1))).2 ∈ Gb'.Ω (k + 1) := fun h' => h (hmem.1 h')
    simp only [h, h', ↓reduceIte]

variable (a : ℕ → ℝ) (aT ν : ℝ)

/-- **The decoupled square root `C^{1/2}(s)`** on the unit points, at corresponding data. -/
theorem decCovSqrt_submatrix (hI : OmegaIso Gb Gb' ρ) {α : Gb.Ω 1 → ℂ} {α' : Gb'.Ω 1 → ℂ}
    (hα : ∀ x, α' (hI.e x) = α x) {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ} (hs : ∀ P ∈ cubeIdx Gb, s' (ck P) = s P)
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hφ : ∀ x : Gb.Ω 1, φ' (hI.e x) = φ x) :
    (decCovSqrt Gb a aT ν α s φ (unitQ Gb) (unitP Gb)).submatrix (eN N hI.unitEquiv.symm)
        (eN N hI.unitEquiv.symm) = decCovSqrt Gb' a aT ν α' s' φ' (unitQ Gb') (unitP Gb') := by
  unfold decCovSqrt
  rw [submatrix_smul_apply, intMat_submatrix]
  congr 2
  funext x
  unfold decSqrtInt
  rw [submatrix_smul_apply, hI.decCov_submatrix a aT x ν hα hs hφ]

/-- **The decoupled square root at the decoupled background** (`hatSqrtF`), at corresponding
parameters and backgrounds. -/
theorem hatSqrtF_submatrix (hI : OmegaIso Gb Gb' ρ) (a₁ : ℝ)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    {F₁' : DecParams Gb' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
    {σ : DecParams Gb} {σ' : DecParams Gb'} (hσ : ∀ q, σ' (hI.cubeEquiv q) = σ q)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N} {Θ' : RawData d L (N₁' * L ^ m₁) (k + 1) N}
    (hF1 : ∀ x i, (F₁' (σ', Θ')).1 (hI.e x, i) = (F₁ (σ, Θ)).1 (x, i))
    (hF2 : ∀ x, (F₁' (σ', Θ')).2 (hI.e x) = (F₁ (σ, Θ)).2 x) :
    (hatSqrtF Gb a₁ ν F₁ σ Θ).submatrix (eN N hI.unitEquiv.symm) (eN N hI.unitEquiv.symm) =
      hatSqrtF Gb' a₁ ν F₁' σ' Θ' := by
  unfold hatSqrtF
  refine hI.decCovSqrt_submatrix (compWeight L a₁) a₁ ν hF2 (fun P hP => hI.extS_self_eq hσ hP)
    (fun x => ?_)
  funext i
  unfold barField
  simp only [coe_e, x.2, hI.mapsTo x.2, ↓reduceDIte]
  exact hF1 x i

/-- The unit blocks of two sites of the box of radius `ρ + 1`. -/
theorem unitBlock_iff_box (hI : OmegaIso Gb Gb' ρ) {x y : CTorus d L N₁ m₁ (k + 1)}
    (hx : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hy : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ (k + 1)) y) :
    unitBlock (bk x) = unitBlock (bk y) ↔ unitBlock x = unitBlock y :=
  (jBlock_boxMap_iff (m₁ := m₁) (j := k) (K := k + 1) (Nat.le_succ k) hI.two_lt.1
    hI.two_lt.2 hx hy).symm

/-- **The extension by zero of corresponding fields of the unit lattices** at the sites of the box
of radius `ρ + 1`. -/
theorem liftZ_eq (hI : OmegaIso Gb Gb' ρ) {v : unitPts Gb × Fin N → ℂ}
    {v' : unitPts Gb' × Fin N → ℂ} (hv : ∀ b i, v' (hI.unitEquiv b, i) = v (b, i))
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    liftZ Gb' v' (bk x) = liftZ Gb v x := by
  have hub : unitBlock (bk x) = bU (unitBlock x) := unitBlock_boxMap hI.two_lt.1 hx
  funext i
  rw [liftZ_apply, liftZ_apply]
  by_cases h : unitBlock x ∈ unitPts Gb
  · have h' : unitBlock (bk x) ∈ unitPts Gb' := by
      rw [hub]; exact hI.mem_unitPts_map ⟨_, h⟩
    simp only [h, h', ↓reduceDIte]
    rw [← hv ⟨_, h⟩ i]
    congr 2
    exact Subtype.ext hub
  · have h' : unitBlock (bk x) ∉ unitPts Gb' := by
      intro h'
      obtain ⟨b, hb⟩ := hI.unitEquiv.surjective ⟨_, h'⟩
      obtain ⟨y, hy⟩ := exists_site b
      have hv1 := congrArg Subtype.val hb
      rw [hI.unitEquiv_site hy, coe_e] at hv1
      have := (hI.unitBlock_iff_box (hI.inBox_succ y.2) hx).1 hv1
      exact h (this ▸ hy ▸ b.2)
    simp only [h, h', ↓reduceDIte]

/-- The coordinate projection on corresponding masks. -/
theorem maskBlock_eq (hI : OmegaIso Gb Gb' ρ) (Zm : Finset (unitPts Gb))
    {w : unitPts Gb × Fin N → ℂ} {w' : unitPts Gb' × Fin N → ℂ}
    (hw : ∀ b i, w' (hI.unitEquiv b, i) = w (b, i)) (b : unitPts Gb) (i : Fin N) :
    maskBlock (Zm.map hI.unitEquiv.toEmbedding) w' (hI.unitEquiv b, i) = maskBlock Zm w (b, i) := by
  unfold maskBlock
  simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply, hw]

/-- **The masked local hat field** at corresponding parameters, backgrounds, hat variables and
masks corresponds on the box of radius `ρ + 1`. -/
theorem markedHatPsiFBg_corr (hI : OmegaIso Gb Gb' ρ) (a₁ : ℝ) (cc : ℂ)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    {F₁' : DecParams Gb' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
    {σ : DecParams Gb} {σ' : DecParams Gb'} (hσ : ∀ q, σ' (hI.cubeEquiv q) = σ q)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N} {Θ' : RawData d L (N₁' * L ^ m₁) (k + 1) N}
    (hF1 : ∀ x i, (F₁' (σ', Θ')).1 (hI.e x, i) = (F₁ (σ, Θ)).1 (x, i))
    (hF2 : ∀ x, (F₁' (σ', Θ')).2 (hI.e x) = (F₁ (σ, Θ)).2 x)
    (Zm : Finset (unitPts Gb)) (um tm : ℂ)
    {ψh : unitPts Gb × Fin N → ℂ} {ψh' : unitPts Gb' × Fin N → ℂ}
    (hψ : ∀ b i, ψh' (hI.unitEquiv b, i) = ψh (b, i)) :
    FieldCorr (ρ + 1) (markedHatPsiFBg Gb a₁ ν (liftZ Gb) cc F₁ Zm um tm σ Θ ψh)
      (markedHatPsiFBg Gb' a₁ ν (liftZ Gb') cc F₁' (Zm.map hI.unitEquiv.toEmbedding) um tm σ' Θ'
        ψh') := by
  have hS := hI.hatSqrtF_submatrix ν a₁ hσ hF1 hF2
  have hM : ∀ p q, (hatSqrtF Gb' a₁ ν F₁' σ' Θ') (eN N hI.unitEquiv p) (eN N hI.unitEquiv q) =
      (hatSqrtF Gb a₁ ν F₁ σ Θ) p q := fun p q => by
    rw [← hS]; simp only [Matrix.submatrix_apply, eN_apply, Equiv.symm_apply_apply, Prod.mk.eta]
  have hv : ∀ b i, (cc • (hatSqrtF Gb' a₁ ν F₁' σ' Θ' *ᵥ ψh')) (hI.unitEquiv b, i) =
      (cc • (hatSqrtF Gb a₁ ν F₁ σ Θ *ᵥ ψh)) (b, i) := fun b i => by
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 1
    exact mulVec_corr_gen (eN N hI.unitEquiv) hM (fun q => hψ q.1 q.2) (b, i)
  intro z hz
  unfold markedHatPsiFBg
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [hI.liftZ_eq hv hz, hI.liftZ_eq (hI.maskBlock_eq Zm hv) hz]

/-- **The data of the fluctuation problem** (`flEdat`) at corresponding backgrounds, data and
fluctuations. -/
theorem flEdat_corr (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ)
    {φα : (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)} {φα' : (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
    (hφ : ∀ x i, φα'.1 (hI.e x, i) = φα.1 (x, i)) (hα : ∀ x, φα'.2 (hI.e x) = φα.2 x)
    {Ψ ψ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {Ψ' ψ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hΨ : FieldCorr (ρ + 1) Ψ Ψ') (hψ : FieldCorr (ρ + 1) ψ ψ') :
    EdatCorr hH (flEdat Gb Hm φα Ψ ψ) (flEdat Gb' Hm' φα' Ψ' ψ') := by
  refine ⟨fun z hz => ?_, fun y => ?_, hψ, fun _ _ => rfl⟩
  · show barField Gb' Ψ' φα'.1 (bk z) = barField Gb Ψ φα.1 z
    funext i
    unfold barField
    by_cases h : z ∈ Gb.Ω 1
    · have h' : bk z ∈ Gb'.Ω 1 := (hI.mem_iff hz).2 h
      simp only [h, h', ↓reduceDIte]
      exact hφ ⟨z, h⟩ i
    · have h' : bk z ∉ Gb'.Ω 1 := fun hh => h ((hI.mem_iff hz).1 hh)
      simp only [h, h', ↓reduceDIte]
      rw [hΨ z hz]
  · show flAlpha Gb' Hm' φα'.2 (hH.e y) = flAlpha Gb Hm φα.2 y
    unfold flAlpha
    have hy := hH.inBox_succ y.2
    by_cases h : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Gb.Ω 1
    · have h' : ((hH.e y : Hm'.Ω 1) : CTorus d L N₁' m₁ (k + 1)) ∈ Gb'.Ω 1 := by
        rw [coe_e]; exact (hI.mem_iff hy).2 h
      simp only [h, h', ↓reduceDIte]
      rw [← hα ⟨_, h⟩]
      rfl
    · have h' : ((hH.e y : Hm'.Ω 1) : CTorus d L N₁' m₁ (k + 1)) ∉ Gb'.Ω 1 := by
        rw [coe_e]; exact fun hh => h ((hI.mem_iff hy).1 hh)
      simp only [h, h', ↓reduceDIte]


/-- **The marked functional of the recomputed terms at corresponding points** (core).  Let `Gb`,
`Hm` be carried onto `Gb'`, `Hm'` by the box map; `σ`, `σ'` the transported parameters of the
canonical transport at the cut parameters `w`, `w'`, corresponding at the top cubes of `Gb`
(`hS`); `D`, `D'` data of `Gb`, `Gb'` corresponding on the box of radius `ρ + 1`; `ψh`, `ψh'` hat
variables whose restrictions correspond at the unit points (`hψ`); the masks `Zm` and its image.
At the point, let the background maps `F₁`, `F₁'` have the uniqueness property of Theorem I-4b
(`hF`, `hF'`) with a solution on the first torus (`hex`), and the fluctuation maps `Sol`, `Sol'`
the properties of Theorem I-4a at the data of the masked hat field (`hv1`–`hv3` on the first torus,
`hv1'` and the uniqueness `hU'` in the ball of radius `r` on the second).  If `Φ'` and `Φ` agree on
corresponding inputs (`hΦ`), the marked functionals agree. -/
theorem FFmarkedBg_canon_eq (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ) (a₁ ρb : ℝ) (cc : ℂ)
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {X₁f' : Finset (CTorus d L N₁' m₁ (k + 1))}
    (w : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
    (w' : ParIdx Gp' (↑X₁f' : Set (CTorus d L N₁' m₁ (k + 1))) → ℂ)
    (hS : ∀ P ∈ cubeIdx Gb, P.2 ∈ Gb.Ω (k + 1) →
      Dec2.extS (coverOf Gp') (extParams Gp' (↑X₁f' : Set (CTorus d L N₁' m₁ (k + 1))) w') (ck P) =
        Dec2.extS (coverOf Gp) (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w) P)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    {F₁' : DecParams Gb' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
    {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf Gb') × Edat Hm' N → (Hm'.Ω 1 × Fin N → ℂ) × (Hm'.Ω 1 → ℂ)}
    {Φ : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : ((Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)) → (Hm'.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (Zm : Finset (unitPts Gb)) (um tm : ℂ)
    {D : BgData Gb N} {D' : BgData Gb' N}
    (hΨ : FieldCorr (ρ + 1) D.Ψ D'.Ψ) (hh : FieldCorr (ρ + 1) D.h D'.h)
    {ψh : unitPts Gp × Fin N → ℂ} {ψh' : unitPts Gp' × Fin N → ℂ}
    (hψ : ∀ b i, resZ Gp' Gb' ψh' (hI.unitEquiv b, i) = resZ Gp Gb ψh (b, i))
    {σ : DecParams Gb} {σ' : DecParams Gb'}
    (hσ : σ = (BgTransport.canon Gp Gb N).par
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w))
    (hσ' : σ' = (BgTransport.canon Gp' Gb' N).par
      (extParams Gp' (↑X₁f' : Set (CTorus d L N₁' m₁ (k + 1))) w'))
    (hF : ∀ φ α, Dec2.IsDecBg (coverOf Gb) Gb (compWeight L a₁) ν ρb σ D φ α →
      F₁ (σ, rawOf D) = (φ, α))
    (hF' : ∀ φ α, Dec2.IsDecBg (coverOf Gb') Gb' (compWeight L a₁) ν ρb σ' D' φ α →
      F₁' (σ', rawOf D') = (φ, α))
    (hex : ∃ φ α, Dec2.IsDecBg (coverOf Gb) Gb (compWeight L a₁) ν ρb σ D φ α)
    {r : ℝ}
    {Rl : Set (((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))}
    {Rl' : Set (((Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)) × (Hm'.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ)))}
    (hv : let p : Dec2.DecParams (coverOf Gb) × Edat Hm N :=
        (σ, flEdat Gb Hm (F₁ (σ, rawOf D)) D.Ψ
          (markedHatPsiFBg Gb a₁ ν (liftZ Gb) cc F₁ Zm um tm σ (rawOf D) (resZ Gp Gb ψh)))
      (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 r ∧ (F₁ (σ, rawOf D), (Sol p).1, (rawOf D, p.2.2.2.1)) ∈ Rl)
    (hv' : let p' : Dec2.DecParams (coverOf Gb') × Edat Hm' N :=
        (σ', flEdat Gb' Hm' (F₁' (σ', rawOf D')) D'.Ψ
          (markedHatPsiFBg Gb' a₁ ν (liftZ Gb') cc F₁' (Zm.map hI.unitEquiv.toEmbedding) um tm σ'
            (rawOf D') (resZ Gp' Gb' ψh')))
      (Sol' p').1 = dphi Hm' (Dec2.decG (coverOf Gb') Hm' (compWeight L a₁) ν p'.1) p'.2.2.1
          p'.2.1 (pertSource Hm' (compWeight L a₁) p'.2.2.2.1 p'.2.2.2.2) (Sol' p').2 ∧
        (∀ δα', Small Hm' δα' r → Dec2.DecFixed (coverOf Gb') Hm' (compWeight L a₁) ν p'.1 false
          p'.2.2.1 p'.2.1 (pertSource Hm' (compWeight L a₁) p'.2.2.2.1 p'.2.2.2.2) δα' →
          δα' = (Sol' p').2) ∧
        (F₁' (σ', rawOf D'), (Sol' p').1, (rawOf D', p'.2.2.2.1)) ∈ Rl')
    (hΦ : ∀ (t : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))
      (t' : ((Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)) × (Hm'.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ))),
      t ∈ Rl → t' ∈ Rl' → (∀ x i, t'.1.1 (hI.e x, i) = t.1.1 (x, i)) → (∀ x, t'.1.2 (hI.e x) = t.1.2 x) →
      (∀ y i, t'.2.1 (hH.e y, i) = t.2.1 (y, i)) →
      FieldCorr (ρ + 1) t.2.2.1.1 t'.2.2.1.1 → FieldCorr (ρ + 1) t.2.2.1.2 t'.2.2.1.2 →
      FieldCorr (ρ + 1) t.2.2.2 t'.2.2.2 → Φ' t'.1 t'.2.1 t'.2.2 = Φ t.1 t.2.1 t.2.2) :
    FFmarkedBg Gp' X₁f' Gb' a₁ ν (BgTransport.canon Gp' Gb' N) cc F₁' Sol' Φ'
        (Zm.map hI.unitEquiv.toEmbedding) um tm (rawOf D', (BgTransport.canon Gp' Gb' N).res ψh') w' =
      FFmarkedBg Gp X₁f Gb a₁ ν (BgTransport.canon Gp Gb N) cc F₁ Sol Φ Zm um tm
        (rawOf D, (BgTransport.canon Gp Gb N).res ψh) w := by
  -- the transported parameters
  have hσc : ∀ q, σ' (hI.cubeEquiv q) = σ q := fun q => by
    rw [hσ, hσ']; exact hI.canon_par_eq hS q
  -- the background values
  obtain ⟨hF1, hF2⟩ := hI.decBg_value_eq hI (compWeight L a₁) ν ρb (s := σ) (s' := σ') hσc hΨ hh
    hF hF' hex
  -- the masked hat fields
  have hψf := hI.markedHatPsiFBg_corr ν a₁ cc hσc hF1 hF2 Zm um tm hψ
  -- the data of the fluctuation problem
  have hE := hI.flEdat_corr hH hF1 hF2 hΨ hψf
  obtain ⟨hv1, hv2, hv3, hvR⟩ := hv
  obtain ⟨hv1', hU', hvR'⟩ := hv'
  obtain ⟨hS1, hS2⟩ := hI.decSol_value_eq hH (compWeight L a₁) ν hσc false hE.α
    (fun x => by rw [coe_e]; exact hE.φ _ (hH.inBox_succ x.2))
    (fun x i => hH.pertSource_eq (compWeight L a₁) hE.δΨ hE.f x i) hv1 hv2 hv3 hv1' hU'
  have hcl : clipRawL Gb (rawOf D) = rawOf D := clipRaw_of_mem_rawSub Gb (rawOf_mem_rawSub D)
  have hcl' : clipRawL Gb' (rawOf D') = rawOf D' := clipRaw_of_mem_rawSub Gb' (rawOf_mem_rawSub D')
  erw [FFmarkedBg_canon_apply X₁f' Gb' a₁ ν cc F₁' Sol' Φ' (Zm.map hI.unitEquiv.toEmbedding) um tm
    (rawOf D', ψh') w', FFmarkedBg_canon_apply X₁f Gb a₁ ν cc F₁ Sol Φ Zm um tm (rawOf D, ψh) w]
  simp only [hcl, hcl', ← hσ, ← hσ']
  exact hΦ (F₁ (σ, rawOf D), _, (rawOf D, _)) (F₁' (σ', rawOf D'), _, (rawOf D', _)) hvR hvR' hF1 hF2
    hS1
    hΨ hh hψf

end OmegaIso

end Balaban.Polymer.LocalIso
