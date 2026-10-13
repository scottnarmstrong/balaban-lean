/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.SFCtxMulti
public import Balaban.Inhabited.QuietHist
public import Balaban.Fluctuation.Thm31Inhab
public import Balaban.LargeField.Def7v2Class
public import Balaban.SmallField.Def6v2Inhabited

/-!
# The fine size of the boundary terms: a boundary domain with finite size and a nonzero term

The landed inhabitants of the records of (D7) (`wBdry`, `wBdry2` before `R`, `wBdryPost`,
`wBdry2Post` after `R`) have boundary terms identically zero, and the histories of
`nonempty_labHist` have no large-field cube, so they have no boundary domain.  This file gives,
in the setting of the Def-7 witness (`d = L = 3`, `M = 27 = 3^{0+3}`, radii `R_j = 32 λ_j²`,
horizon `K = 1`, scale `k = 1`, regime index `k₀ = 0`), on the torus with `n_1 = 2 r + 4` cubes
per side, `r = ⌊2 R_0⌋ + 2 L + 6`:

* `labBdry`: the history with one large-field cube created at the step `0 → 1` (`QuietHist`).  Its
  region `Z_1` contains the cube `0` (`labBdry_zero_mem_Z`) and lies in the neighbourhood of
  radius `⌊2 R_0⌋ + 2 L + 7` of that cube (`quiet_regions_one_subset`; for `k₀ = 0` there is no
  hull closure), so it misses the cube `farCube` (`farCube_not_mem_Z`).
* `labBdry_univ_mem_bdryDomsPost`: the set of all cubes is a boundary domain of the post-`R`
  class at this history (it meets `Z_1` and its complement, and its fine set is the whole fine
  torus, a member of `𝒟_1(mod Ω_f^c)`); `d7SizeE_univ_ne_top`: its fine size is finite.
* `repBdry`, `repBdry_d7`, `exists_d7BdryPost_nonzero`: a representation with the single history
  `labBdry` whose boundary term at that domain is the nonzero constant
  `(fac / 2) e^{-rate · d7Size}` and `0` at the other domains; it satisfies `D7Bdry2Post` and
  `D7BdryPost`, the bound being `(fac / 2) e^{-rate · d7Size} < fac · e^{-rate · d7Size}`.
* `labBdry_univ_mem_bdryDomsPre`, `d7SizePreE_ne_top_at_boundary_domain`,
  `exists_d7Bdry_nonzero`: the same for the pre-`R` record `D7Bdry` (region `Z^pre_1 = Z_1`,
  raw region; no component of `labBdry` is removed, so the two records coincide).

* `corner_dCovMod_zero_fine_top`: for two blocks of cubes meeting at a corner, the cube-level
  size `dCovMod` is `0` and the fine size `Fluctuation.dcovModE` is `⊤`
  (`dCovMod_eq_zero_of_point`, `dcovModE_eq_top_of_separated`).

**Not proved here.**  The size of this domain is finite; that it is positive is not proved.  The
representation is an inhabitant of the record (D7) only: it is not completed to an inhabitant of
`IsRep` (its set of histories is a singleton, not a complete set, and `k₀ = 0`).  For `k₀ ≥ 1`
the region `Z^pre_1` is the hull closure of `Z^{(0)}_1`, and no upper bound on a hull closure is
used here.
-/

@[expose] public section

namespace Balaban.LargeField.Def7

open Balaban Balaban.LargeField Balaban.Localization Balaban.LargeField.Def7.Wit Balaban.Inhabited
  Balaban.LargeField.Def7v2 RegionHistory

/-! ### The region of the history with one large-field cube -/

section Generic

variable {S : Setting} [NeZero S.L] {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ}

/-- The cube `0` created at the step `0 → 1` belongs to `Z^pre_1`. -/
theorem quiet_zero_mem_regions_one (k0 : ℕ) :
    (0 : Torus S.d (n 1)) ∈ QuietHist.regions S n R k0 1 :=
  (QuietHist.mkStep (S := S) (n := n) (R := R) 0 (QuietHist.regions S n R k0 0)).Z0_subset_Zpre
    (S.omega 1) (critOpt S k0 1)
    ((QuietHist.mkStep (S := S) (n := n) (R := R) 0
      (QuietHist.regions S n R k0 0)).newCubes_subset_Z0 (Or.inl (Or.inl (Or.inl ⟨rfl, rfl, rfl⟩))))

/-- For `k₀ = 0` (no hull closure) the region `Z^pre_1 = Z^{(0)}_1` created by the single cube
`0` lies in the neighbourhood of radius `⌊2 R_0⌋ + 2 L + 7` of that cube: `Ω'_1 = 𝕋_1`,
`Ω'_1 ∖ Ω_1 ⊆ P^{∼(L+2)}`, `Ω''_1 = Ω_1`, `F^Z ⊆ (Ω''^c)^{∼4}` and
`Z^{(0)} ⊆ (F^Z)^{∼(⌊2R_0⌋ + L + 1)}` (Lemma I.3.5). -/
theorem quiet_regions_one_subset :
    QuietHist.regions S n R 0 1 ⊆
      nbhd (⌊2 * R 0⌋₊ + 2 * S.L + 7) ({0} : Set (Torus S.d (n 1))) := by
  have hL : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne S.L)
  set st := QuietHist.mkStep (S := S) (n := n) (R := R) 0 (QuietHist.regions S n R 0 0) with hst
  have h1 : QuietHist.regions S n R 0 1 = st.Z0 := by
    show Region.Zpre (S.omega 1) (critOpt S 0 1) st.Z0 = st.Z0
    have : critOpt S 0 1 = none := by simp [critOpt]
    rw [this]; rfl
  have hP : st.P ⊆ ({0} : Set (Torus S.d (n 1))) := fun x hx => hx.2.2
  have hOP : st.OmegaPrime = Set.univ := omegaPrime_of_empty _ _
  have hDD : st.OmegaDDᶜ ⊆ nbhd (S.L + 2) ({0} : Set (Torus S.d (n 1))) := by
    intro x hx
    by_cases hxO : x ∈ st.Omega
    · have := st.Omega_diff_OmegaDD_subset hL ⟨hxO, hx⟩
      have hQ : st.Q = ∅ := rfl
      have hR : st.R = ∅ := rfl
      rw [hQ, hR, nbhd_empty, nbhd_empty] at this
      exact absurd this (by simp)
    · have hx' : x ∈ st.OmegaPrime \ st.Omega := ⟨by rw [hOP]; trivial, hxO⟩
      exact nbhd_mono le_rfl hP (st.OmegaPrime_diff_Omega_subset hL hx')
  have hFZ : st.FZ ⊆ nbhd (S.L + 2 + 4) ({0} : Set (Torus S.d (n 1))) := by
    intro x hx
    have hS : st.S = ∅ := rfl
    rcases hx with hx | hx
    · rw [← nbhd_nbhd]; exact nbhd_mono le_rfl hDD hx
    · rw [hS, nbhd_empty] at hx; exact absurd hx (by simp)
  rw [h1]
  intro x hx
  have h2 := nbhd_mono le_rfl hFZ (st.Z0_subset_nbhd_FZ hL hx)
  rw [nbhd_nbhd] at h2
  refine nbhd_mono ?_ subset_rfl h2
  omega

/-- The whole torus of cubes is a valid label for every frame and region. -/
theorem fineValidAt_univ {K M m₀ m₁ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) (k : ℕ)
    (Om : Set (Torus S.d (n k))) :
    FineValidAt F k Om (Finset.univ : Finset (Torus S.d (n k))) := by
  refine fineValidAt_of_djMod ⟨?_, fun z _ => Or.inl ?_⟩
  · rw [Finset.coe_univ, d7Pull_univ]
    exact Fluctuation.isDj_univ _ _ _ _ _ _ _
  · rw [Finset.coe_univ, d7Pull_univ]
    exact Set.subset_univ _

/-- The whole torus of cubes is a valid label after `R`, for every frame and history. -/
theorem fineValid_univ {R : ℕ → ℝ} {k0 K M m₀ m₁ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (A : LabHist S n R k0 K) (k : ℕ) :
    FineValid F A k (Finset.univ : Finset (Torus S.d (n k))) :=
  fineValidAt_univ F k _

/-- The whole torus of cubes is a valid label before `R`, for every frame and history. -/
theorem fineValidPre_univ {R : ℕ → ℝ} {k0 K M m₀ m₁ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (A : LabHist S n R k0 K) (k : ℕ) :
    FineValidPre F A k (Finset.univ : Finset (Torus S.d (n k))) :=
  fineValidAt_univ F k _

/-- The whole torus of cubes is a domain of `𝒟_k(mod Ω^c)` for every `Ω`. -/
theorem dmodOmega_univ {d N : ℕ} [NeZero N] (Om : Set (Torus d N)) :
    DmodOmega Om (Finset.univ : Finset (Torus d N)) := by
  refine ⟨⟨Finset.univ_nonempty, fun x _ y _ => ?_⟩, fun a _ => Or.inl ?_⟩
  · exact Relation.ReflTransGen.mono
      (fun a b h => ⟨Finset.mem_univ _, Finset.mem_univ _, h.2.2⟩) x y
      (Balaban.SmallField.Def6v2.torus_reach x y)
  · rw [Finset.coe_univ]; exact Set.subset_univ _

end Generic

/-! ### The history and its boundary domain -/

section Instance

/-- The radius `r = ⌊2 R_0⌋ + 2 L + 6`: `Z_1` lies in the `(r + 1)`-neighbourhood of the cube
`0`. -/
noncomputable def rBdry : ℕ := ⌊2 * wR 0⌋₊ + 2 * wS.L + 6

/-- The number `2 r + 4` of cubes per side of the scale-`1` torus. -/
noncomputable def nBdry : ℕ := 2 * rBdry + 4

instance : NeZero nBdry := ⟨by unfold nBdry; omega⟩

theorem sides_nBdry : sides wS.L 1 nBdry 1 = 2 * rBdry + 4 := by
  simp [sides, nBdry]

/-- The region history with one large-field cube created at the step `0 → 1`, on the torus with
`n_1 = 2 r + 4`, with `k₀ = 0` and horizon `K = 1`. -/
noncomputable def histBdry : RegionHistory wS (sides wS.L 1 nBdry) wR 0 1 :=
  QuietHist.hist (k0 := 0) wS_ok le_rfl le_rfl wRH (sides_hnn wS.L 1 nBdry)

/-- The history `histBdry` with its (empty) `R`-records. -/
noncomputable def labBdry : LabHist wS (sides wS.L 1 nBdry) wR 0 1 :=
  ⟨histBdry, fun _ c hc => by simp [histBdry, QuietHist.hist] at hc, fun _ _ => 0⟩

theorem labBdry_Z : (labBdry.H.step 1).Z = QuietHist.regions wS (sides wS.L 1 nBdry) wR 0 1 := rfl

/-- `Z_1` is not empty. -/
theorem labBdry_zero_mem_Z :
    (0 : Torus wS.d (sides wS.L 1 nBdry 1)) ∈ (labBdry.H.step 1).Z := by
  rw [labBdry_Z]; exact quiet_zero_mem_regions_one 0

/-- The cube at index distance `r + 2` from the cube `0` in the first direction. -/
noncomputable def farCube : Torus wS.d (sides wS.L 1 nBdry 1) :=
  Function.update 0 ⟨0, by norm_num [wS, setting, typing, typing0]⟩ ((rBdry + 2 : ℕ) : ZMod _)

/-- `Z_1` is not the whole torus. -/
theorem farCube_not_mem_Z : farCube ∉ (labBdry.H.step 1).Z := by
  rw [labBdry_Z]
  intro h
  have h1 := quiet_regions_one_subset h
  exact far_not_mem_thick sides_nBdry _ h1

/-- The set of all cubes is a boundary domain at the raw region `Ω_1^pre`: it is a term of the
sum `Rep.bdrySum` of (D1). -/
theorem labBdry_univ_mem_bdryDoms :
    (Finset.univ : Finset (Torus wS.d (sides wS.L 1 nBdry 1))) ∈
      bdryDoms (OmegaCube labBdry.H 1) ((labBdry.H.step 1).Z) := by
  rw [mem_bdryDoms]
  refine ⟨dmodOmega_univ _, ⟨0, ?_, labBdry_zero_mem_Z⟩, ⟨farCube, ?_, farCube_not_mem_Z⟩⟩
  · simp
  · simp

/-- **The set of all cubes is a boundary domain of the post-`R` class** at the history `labBdry`:
it belongs to `𝒟_1(mod (Ω_1^post)^c)`, meets `Z_1` (at the cube `0`) and its complement (at
`farCube`), and is `FineValid`. -/
theorem labBdry_univ_mem_bdryDomsPost :
    (Finset.univ : Finset (Torus wS.d (sides wS.L 1 nBdry 1))) ∈
      bdryDomsPost (wFrame nBdry) labBdry 1 ((labBdry.H.step 1).Z) :=
  mem_bdryDomsPost.2 ⟨bdryDoms_OmegaCube_subset_omegaPost _ _ _ labBdry_univ_mem_bdryDoms,
    fineValid_univ _ _ _⟩

/-- The fine size of this boundary domain is finite. -/
theorem d7SizeE_univ_ne_top : d7SizeE (wFrame nBdry) labBdry 1
    (Finset.univ : Finset (Torus wS.d (sides wS.L 1 nBdry 1))) ≠ ⊤ :=
  d7SizeE_ne_top_of_mem labBdry_univ_mem_bdryDomsPost

/-- **The fine size is finite at a boundary domain of a history with a large-field region**, on a
torus with more than one cube per side: there is a nonempty boundary domain `X` of the post-`R`
class at `labBdry` (so `X ∩ Z_1 ≠ ∅ ≠ X ∖ Z_1`) with `d7SizeE ≠ ⊤`. -/
theorem d7SizeE_ne_top_at_boundary_domain :
    2 ≤ sides wS.L 1 nBdry 1 ∧
      ∃ X ∈ bdryDomsPost (wFrame nBdry) labBdry 1 ((labBdry.H.step 1).Z),
        X.Nonempty ∧ d7SizeE (wFrame nBdry) labBdry 1 X ≠ ⊤ :=
  ⟨by rw [sides_nBdry]; omega,
    Finset.univ, labBdry_univ_mem_bdryDomsPost, Finset.univ_nonempty, d7SizeE_univ_ne_top⟩

/-- `Z^pre_1 = Z_1` for this history (no component is removed). -/
theorem labBdry_Zpre : labBdry.H.F.Zpre 1 = (labBdry.H.step 1).Z := by
  rw [labBdry_Z]
  exact QuietHist.flowSteps_Zpre (k0 := 0) wS_ok le_rfl le_rfl wRH (sides_hnn wS.L 1 nBdry) 1

/-- **The set of all cubes is a boundary domain of the pre-`R` class** at the history `labBdry`
(region `Z^pre_1`, raw region `Ω_1^pre`). -/
theorem labBdry_univ_mem_bdryDomsPre :
    (Finset.univ : Finset (Torus wS.d (sides wS.L 1 nBdry 1))) ∈
      bdryDomsPre (wFrame nBdry) labBdry 1 (labBdry.H.F.Zpre 1) := by
  rw [labBdry_Zpre]
  exact mem_bdryDomsPre.2 ⟨labBdry_univ_mem_bdryDoms, fineValidPre_univ _ _ _⟩

/-- **The fine size before `R` is finite at a boundary domain of a history with a large-field
region**, on a torus with more than one cube per side. -/
theorem d7SizePreE_ne_top_at_boundary_domain :
    2 ≤ sides wS.L 1 nBdry 1 ∧
      ∃ X ∈ bdryDomsPre (wFrame nBdry) labBdry 1 (labBdry.H.F.Zpre 1),
        X.Nonempty ∧ d7SizePreE (wFrame nBdry) labBdry 1 X ≠ ⊤ :=
  ⟨by rw [sides_nBdry]; omega,
    Finset.univ, labBdry_univ_mem_bdryDomsPre, Finset.univ_nonempty,
    d7SizePreE_ne_top_of_mem labBdry_univ_mem_bdryDomsPre⟩

/-! ### A nonzero boundary term satisfying the bound -/

/-- The constant `(fac / 2) e^{-rate · d7Size}` at the boundary domain of all cubes. -/
noncomputable def cBdry (fac rate : ℝ) : ℝ :=
  fac / 2 * Real.exp (-rate * d7Size (wFrame nBdry) labBdry 1 Finset.univ)

theorem cBdry_pos {fac : ℝ} (rate : ℝ) (hfac : 0 < fac) : 0 < cBdry fac rate := by
  unfold cBdry; positivity

theorem cBdry_lt {fac : ℝ} (rate : ℝ) (hfac : 0 < fac) :
    cBdry fac rate < fac * Real.exp (-rate * d7Size (wFrame nBdry) labBdry 1 Finset.univ) := by
  unfold cBdry
  have := Real.exp_pos (-rate * d7Size (wFrame nBdry) labBdry 1 Finset.univ)
  nlinarith [mul_pos hfac this]

/-- A representation with the single history `labBdry`, zero step and kept data, and the
boundary terms `ℬ(X) = (fac / 2) e^{-rate · d7Size}` at the domain `X` of all cubes and `0` at
the other domains. -/
noncomputable def repBdry (ν fac rate : ℝ) :
    Rep wS (sides wS.L 1 nBdry) wR 0 1 27 2 (wGeoF nBdry) (wCs ν 0) (budgetConsts wβ) 1 where
  hist := {labBdry}
  κK := fun _ _ => 0
  SD := zeroStepData (wGeoF nBdry) (wCs ν 0) le_rfl rfl _
  KD := zeroKeptData (wGeoF nBdry) (wCs ν 0) _ _
  B := fun _ X _ _ _ _ => if X = Finset.univ then ((cBdry fac rate : ℝ) : ℂ) else 0

theorem repBdry_B (ν fac rate : ℝ) (A : LabHist wS (sides wS.L 1 nBdry) wR 0 1)
    (X : Finset (Torus wS.d (sides wS.L 1 nBdry 1)))
    (ψ ψ' : MultiFieldC wS (sides wS.L 1 nBdry) 27 1 2) (h : Fin 2 → ℂ)
    (g : GIdx wS (sides wS.L 1 nBdry) 27 1 2 → ℂ) :
    (repBdry ν fac rate).B A X ψ ψ' h g =
      if X = Finset.univ then ((cBdry fac rate : ℝ) : ℂ) else 0 := rfl

/-- **`repBdry` satisfies (D7) of the post-`R` class, second version**, for every pinned radius:
the boundary terms are constants, the bound at the domain of all cubes is
`(fac / 2) e^{-rate · d7Size} < fac · e^{-rate · d7Size}`, and the terms vanish off the valid
labels because the domain of all cubes is valid. -/
theorem repBdry_d7 (ν : ℝ)
    (Zof : LabHist wS (sides wS.L 1 nBdry) wR 0 1 → Set (Torus wS.d (sides wS.L 1 nBdry 1)))
    (aw μs ε ε1 νs : ℕ → ℝ) {fac : ℝ} (rate : ℝ) (hfac : 0 < fac) (rH : ℝ) :
    D7Bdry2Post (wFrame nBdry) (sides_hnn wS.L 1 nBdry) le_rfl (repBdry ν fac rate)
      Zof aw μs ε ε1 νs fac rate whv rH where
  loc_field := by intros; rfl
  loc_hist := by intros; rfl
  real := by
    intro A _ X _ ψ ψ' h g _ _ _
    rw [repBdry_B]
    split_ifs <;> simp
  analytic := fun _ _ _ _ _ _ => analyticOnNhd_const
  bound := by
    intro A hA X hX h _ p _
    obtain rfl : A = labBdry := Finset.mem_singleton.1 hA
    rw [repBdry_B]
    split_ifs with hXu
    · subst hXu
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cBdry_pos rate hfac)]
      exact cBdry_lt rate hfac
    · rw [norm_zero]; positivity
  rot := by intros; rfl
  euclid := by
    intro A _ A' _ σ _ _ X _ ψ ψ' h g
    rw [repBdry_B, repBdry_B]
    have hiff : X.map (σ.ec 1).toEmbedding = Finset.univ ↔ X = Finset.univ := by
      constructor
      · intro hm
        refine Finset.eq_univ_iff_forall.2 fun y => ?_
        have hy : (σ.ec 1) y ∈ X.map (σ.ec 1).toEmbedding := by rw [hm]; exact Finset.mem_univ _
        obtain ⟨x, hx, hxy⟩ := Finset.mem_map.1 hy
        exact (σ.ec 1).injective hxy ▸ hx
      · rintro rfl
        exact Finset.map_univ_equiv _
    simp only [hiff]
  support := by
    intro A _ X _ hnv ψ ψ' h g
    rw [repBdry_B]
    split_ifs with hXu
    · exact absurd (hXu ▸ fineValid_univ (wFrame nBdry) A 1) hnv
    · rfl

/-- **(D7) of the post-`R` class has an inhabitant with a boundary term that is not identically
zero**: a representation satisfying `D7Bdry2Post` for every pinned radius and `D7BdryPost`, a
history of it and a boundary domain of the post-`R` class at which the boundary term is nonzero
at all arguments (and whose fine size is finite). -/
theorem exists_d7BdryPost_nonzero (ν : ℝ) (aw μs ε ε1 νs : ℕ → ℝ) {fac : ℝ} (rate : ℝ)
    (hfac : 0 < fac) :
    ∃ rep : Rep wS (sides wS.L 1 nBdry) wR 0 1 27 2 (wGeoF nBdry) (wCs ν 0) (budgetConsts wβ) 1,
      (∀ rH : ℝ, D7Bdry2Post (wFrame nBdry) (sides_hnn wS.L 1 nBdry) le_rfl rep
        (fun A => (A.H.step 1).Z) aw μs ε ε1 νs fac rate whv rH) ∧
      D7BdryPost (wFrame nBdry) (sides_hnn wS.L 1 nBdry) le_rfl rep
        (fun A => (A.H.step 1).Z) aw μs ε ε1 νs fac rate whv ∧
      ∃ A ∈ rep.hist, ∃ X ∈ bdryDomsPost (wFrame nBdry) A 1 ((A.H.step 1).Z),
        d7SizeE (wFrame nBdry) A 1 X ≠ ⊤ ∧
          ∀ (ψ ψ' : MultiFieldC wS (sides wS.L 1 nBdry) 27 1 2) (h : Fin 2 → ℂ)
            (g : GIdx wS (sides wS.L 1 nBdry) 27 1 2 → ℂ), rep.B A X ψ ψ' h g ≠ 0 := by
  refine ⟨repBdry ν fac rate, fun rH => repBdry_d7 ν _ aw μs ε ε1 νs rate hfac rH,
    (repBdry_d7 ν _ aw μs ε ε1 νs rate hfac 1).toD7BdryPost one_pos,
    labBdry, Finset.mem_singleton_self _, Finset.univ, labBdry_univ_mem_bdryDomsPost,
    d7SizeE_univ_ne_top, fun ψ ψ' h g => ?_⟩
  simp only [repBdry_B, ↓reduceIte]
  exact_mod_cast (cBdry_pos rate hfac).ne'

/-- **(D7) of the pre-`R` class has an inhabitant with a boundary term that is not identically
zero**: the representation `repBdry` (no component of its history is removed, so its two records
coincide, `d7Bdry_iff_d7BdryPost_of_rem_empty`) satisfies `D7Bdry` for the region `Z^pre_1`, and
its boundary term at the boundary domain of all cubes is nonzero. -/
theorem exists_d7Bdry_nonzero (ν : ℝ) (aw μs ε ε1 νs : ℕ → ℝ) {fac : ℝ} (rate : ℝ)
    (hfac : 0 < fac) :
    ∃ rep : Rep wS (sides wS.L 1 nBdry) wR 0 1 27 2 (wGeoF nBdry) (wCs ν 0) (budgetConsts wβ) 1,
      D7Bdry (wFrame nBdry) (sides_hnn wS.L 1 nBdry) le_rfl rep
        (fun A => A.H.F.Zpre 1) aw μs ε ε1 νs fac rate whv ∧
      ∃ A ∈ rep.hist, ∃ X ∈ bdryDomsPre (wFrame nBdry) A 1 (A.H.F.Zpre 1),
        d7SizePreE (wFrame nBdry) A 1 X ≠ ⊤ ∧
          ∀ (ψ ψ' : MultiFieldC wS (sides wS.L 1 nBdry) 27 1 2) (h : Fin 2 → ℂ)
            (g : GIdx wS (sides wS.L 1 nBdry) 27 1 2 → ℂ), rep.B A X ψ ψ' h g ≠ 0 := by
  have hrem : ∀ A ∈ (repBdry ν fac rate).hist, A.H.rem 1 = ∅ := by
    intro A hA
    obtain rfl : A = labBdry := Finset.mem_singleton.1 hA
    rfl
  refine ⟨repBdry ν fac rate, (d7Bdry_iff_d7BdryPost_of_rem_empty hrem).2
      ((repBdry_d7 ν _ aw μs ε ε1 νs rate hfac 1).toD7BdryPost one_pos),
    labBdry, Finset.mem_singleton_self _, Finset.univ, labBdry_univ_mem_bdryDomsPre,
    d7SizePreE_ne_top_of_mem labBdry_univ_mem_bdryDomsPre, fun ψ ψ' h g => ?_⟩
  simp only [repBdry_B, ↓reduceIte]
  exact_mod_cast (cBdry_pos rate hfac).ne'

end Instance

/-! ### The corner configuration: cube-level size `0`, fine size `⊤` -/

section Corner

/-- If a single point of the continuous torus lies in a closed cube of `X` and in a closed cube
of every chosen block, the cube-level size is `0`. -/
theorem dCovMod_eq_zero_of_point {d n : ℕ} [NeZero n] {L : ℕ} {Ω : Set (Torus d n)}
    {X : Finset (Torus d n)} {𝒦 : Set (Torus d n)}
    (h𝒦 : ∀ c ∈ 𝒦, (∀ i, L ∣ (c i).val) ∧ lblock L c ⊆ (X : Set (Torus d n)))
    (hcov : ∀ x ∈ X, x ∈ Ω → ∃ c ∈ 𝒦, x ∈ lblock L c)
    {p : LargeField.CTorus d n} (hpX : ∃ x ∈ X, p ∈ cube x)
    (hp : ∀ c ∈ 𝒦, ∃ y ∈ lblock L c, p ∈ cube y) :
    dCovMod L Ω X = 0 := by
  classical
  set s : Seg d n := ⟨p, fun _ => 0⟩ with hs
  have hcar : (⋃ s' ∈ ({s} : Finset (Seg d n)), s'.carrier) = {p} := by
    ext q
    simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left, Set.mem_singleton_iff]
    constructor
    · rintro ⟨t, -, ht⟩
      funext i
      simpa [hs] using ht i
    · rintro rfl
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, fun i => by simp [hs]⟩
  have hadm : IsCovCurve L Ω X 𝒦 {s} := by
    refine ⟨h𝒦, hcov, ?_, ?_, ?_⟩
    · rw [hcar]; exact isConnected_singleton
    · rw [hcar]
      obtain ⟨x, hx, hpx⟩ := hpX
      exact Set.singleton_subset_iff.2 (Set.mem_iUnion₂.2 ⟨x, hx, hpx⟩)
    · intro c hc
      obtain ⟨y, hy, hpy⟩ := hp c hc
      exact ⟨y, hy, p, by rw [hcar]; rfl, hpy⟩
  have hlen : ∑ s' ∈ ({s} : Finset (Seg d n)), s'.length = 0 := by
    simp [hs, Seg.length]
  refine le_antisymm ?_ zero_le
  calc dCovMod L Ω X ≤ ENNReal.ofReal (∑ s' ∈ ({s} : Finset (Seg d n)), s'.length) :=
        iInf_le_of_le 𝒦 (iInf_le_of_le {s} (iInf_le_of_le hadm le_rfl))
    _ = 0 := by rw [hlen, ENNReal.ofReal_zero]

private theorem no_admissible_aux {d L N₁ m₁ K m₀ j : ℕ}
    {Ω P Q 𝒦 : Set (Localization.CTorus d L N₁ m₁ K)}
    {W : Finset (Localization.CTorus d L N₁ m₁ K)}
    {E : Finset (Localization.CTorus d L N₁ m₁ K × Localization.CTorus d L N₁ m₁ K)}
    (hdisj : Disjoint P Q) (hsep : ∀ x ∈ P, ∀ y ∈ Q, ¬ Nbr x y) (hQ : (Q ∩ Ω).Nonempty)
    (h : Fluctuation.ModAdmissible m₀ j Ω (P ∪ Q) 𝒦 W E)
    {w₀ : Localization.CTorus d L N₁ m₁ K} (hw₀ : w₀ ∈ W) (hw₀P : w₀ ∈ P) : False := by
  obtain ⟨h𝒦, hcov, hconn, hWX, hmeet⟩ := h
  have stay : ∀ {u v : Localization.CTorus d L N₁ m₁ K},
      Relation.ReflTransGen (fun a b => a ∈ P ∪ Q ∧ b ∈ P ∪ Q ∧ Nbr a b) u v → u ∈ P → v ∈ P := by
    intro u v huv hu
    induction huv with
    | refl => exact hu
    | tail _ hbc ih => exact hbc.2.1.resolve_right (fun hc => hsep _ ih _ hc hbc.2.2)
  have hWP : ∀ w ∈ W, w ∈ P := by
    intro w hw
    refine stay (Relation.ReflTransGen.mono (fun a b hab => ?_) w₀ w (hconn.2.2 w₀ hw₀ w hw)) hw₀P
    rcases hab with hab | hab
    · obtain ⟨ha, hb, hn⟩ := hconn.2.1 _ hab
      exact ⟨hWX ha, hWX hb, hn⟩
    · obtain ⟨hb, ha, hn⟩ := hconn.2.1 _ hab
      exact ⟨hWX ha, hWX hb, hn.symm⟩
  obtain ⟨z, hzQ, hzΩ⟩ := hQ
  obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.1 (hcov ⟨Or.inr hzQ, hzΩ⟩)
  obtain ⟨x, hxW, hxb⟩ := hmeet b hb
  have hchain := chain_in_box b _ (P ∪ Q) (h𝒦 b hb).2 hxb hzb
  have hzP : z ∈ P := stay (Relation.ReflTransGen.mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1.2⟩) x z hchain) (hWP x hxW)
  exact Set.disjoint_left.1 hdisj hzP hzQ

/-- If `X` is the union of two disjoint parts, each meeting `Ω`, with no nearest-neighbour bond
between them, the fine size of `X` modulo `Ω^c` is `⊤`. -/
theorem dcovModE_eq_top_of_separated {d L N₁ m₁ K m₀ j : ℕ}
    {Ω A B : Set (Localization.CTorus d L N₁ m₁ K)} (hdisj : Disjoint A B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, ¬ Nbr x y) (hA : (A ∩ Ω).Nonempty) (hB : (B ∩ Ω).Nonempty) :
    Fluctuation.dcovModE m₀ j Ω (A ∪ B) = ⊤ := by
  by_contra hne
  obtain ⟨𝒦, W, E, h⟩ := Fluctuation.exists_admissible_of_ne_top hne
  obtain ⟨w₀, hw₀⟩ := h.2.2.1.1
  rcases h.2.2.2.1 hw₀ with hw | hw
  · exact no_admissible_aux hdisj hsep hB h hw₀ hw
  · rw [Set.union_comm] at h
    exact no_admissible_aux hdisj.symm (fun x hx y hy hn => hsep y hy x hx hn.symm) hA h hw₀ hw


/-- The two `2 × 2` blocks of cubes of `𝕋 = (ℤ/4)²` with corners `(0,0)` and `(2,2)`. -/
def cornerX : Finset (Torus 2 4) :=
  Finset.univ.filter fun x => (∀ i, (x i).val < 2) ∨ (∀ i, 2 ≤ (x i).val)

theorem mem_cornerX {x : Torus 2 4} :
    x ∈ cornerX ↔ (∀ i, (x i).val < 2) ∨ (∀ i, 2 ≤ (x i).val) := by
  simp [cornerX]

/-- The cube-level size of the two blocks is `0`: the corner point `(2,2)` of the continuous torus
lies in the closed cubes `□_{(1,1)}` and `□_{(2,2)}`, one in each block. -/
theorem cornerX_dCovMod : dCovMod 2 (Set.univ : Set (Torus 2 4)) cornerX = 0 := by
  have h2 : ((2 : ZMod 4)).val = 2 := by decide
  refine dCovMod_eq_zero_of_point (𝒦 := {0, fun _ => 2}) (p := fun _ => zc (2 : ZMod 4))
    ?_ ?_ ?_ ?_
  · rintro c (rfl | rfl)
    · refine ⟨fun i => by simp, ?_⟩
      rintro y ⟨v, hv, rfl⟩
      refine mem_cornerX.2 (Or.inl fun i => ?_)
      have := hv i
      show ((0 : ZMod 4) + ((v i : ℕ) : ZMod 4)).val < 2
      rw [zero_add, ZMod.val_natCast_of_lt (by omega)]
      exact this
    · refine ⟨fun i => by simp [h2], ?_⟩
      rintro y ⟨v, hv, rfl⟩
      refine mem_cornerX.2 (Or.inr fun i => ?_)
      have := hv i
      have e : (2 : ZMod 4) + ((v i : ℕ) : ZMod 4) = ((2 + v i : ℕ) : ZMod 4) := by
        push_cast; rfl
      show 2 ≤ ((2 : ZMod 4) + ((v i : ℕ) : ZMod 4)).val
      rw [e, ZMod.val_natCast_of_lt (by omega)]
      omega
  · intro x hx _
    rcases mem_cornerX.1 hx with h | h
    · refine ⟨0, Or.inl rfl, fun i => (x i).val, h, ?_⟩
      funext i; simp
    · refine ⟨fun _ => 2, Or.inr rfl, fun i => (x i).val - 2, fun i => ?_, ?_⟩
      · have := ZMod.val_lt (x i)
        show (x i).val - 2 < 2
        omega
      · funext i
        have h1 := h i
        have h3 : (((x i).val - 2 : ℕ) : ZMod 4) = ((x i).val : ZMod 4) - 2 := by
          rw [Nat.cast_sub h1]; rfl
        rw [h3]; simp
  · exact ⟨fun _ => 2, mem_cornerX.2 (Or.inr fun i => by simp [h2]),
      fun i => ⟨0, by simp, by simp⟩⟩
  · rintro c (rfl | rfl)
    · refine ⟨fun _ => 1, ⟨fun _ => 1, fun _ => by norm_num, by funext i; simp⟩,
        fun i => ⟨1, by simp, ?_⟩⟩
      have e2 : zc (2 : ZMod 4) = (((2 : ℕ) : ℝ) : AddCircle ((4 : ℕ) : ℝ)) := zc_natCast 2
      have e1 : zc (1 : ZMod 4) = (((1 : ℕ) : ℝ) : AddCircle ((4 : ℕ) : ℝ)) := by
        simpa using zc_natCast (n := 4) 1
      show zc (2 : ZMod 4) = zc (1 : ZMod 4) + _
      rw [e2, e1, ← AddCircle.coe_add]
      norm_num
    · exact ⟨fun _ => 2, ⟨fun _ => 0, fun _ => by norm_num, by funext i; simp⟩,
        fun i => ⟨0, by simp, by simp⟩⟩

/-- The fine size of the two blocks is `⊤`: with `m₀ = m₁ = 0`, `K = 0` and scale `j = 0` the cells
are single sites, the fine torus is `𝕋 = (ℤ/4)²` itself and the `π'`-cubes are the `2 × 2` blocks;
there is no nearest-neighbour bond between the two blocks. -/
theorem cornerX_fine :
    Fluctuation.dcovModE (d := 2) (L := 2) (N₁ := 4) (m₁ := 0) (K := 0) 0 0
      (Set.univ : Set (Localization.CTorus 2 2 4 0 0)) (cornerX : Set (Torus 2 4)) = ⊤ := by
  have hX : (cornerX : Set (Torus 2 4)) =
      {x : Torus 2 4 | ∀ i, (x i).val < 2} ∪ {x : Torus 2 4 | ∀ i, 2 ≤ (x i).val} := by
    ext x; simp [mem_cornerX]
  rw [hX]
  refine dcovModE_eq_top_of_separated ?_ ?_
    ⟨0, fun i => by show ((0 : ZMod 4)).val < 2; decide, trivial⟩ ⟨fun _ => 2, ?_, trivial⟩
  · refine Set.disjoint_left.2 fun x hx hx' => ?_
    have := hx 0; have := hx' 0; omega
  · rintro x hx y hy ⟨μ, h | h⟩
    · obtain ⟨i, hi⟩ := exists_ne μ
      have e : y i = x i := by rw [h]; simp [Pi.single_eq_of_ne hi]
      have := hx i; have := hy i; rw [e] at *; omega
    · obtain ⟨i, hi⟩ := exists_ne μ
      have e : x i = y i := by rw [h]; simp [Pi.single_eq_of_ne hi]
      have := hx i; have := hy i; rw [e] at *; omega
  · intro i; show 2 ≤ ((2 : ZMod 4)).val; decide

/-- **The corner configuration** (`notes/phase1/VMOD-25.md` §2, without the detour): for the two
`2 × 2` blocks of `(ℤ/4)²` meeting at a corner, with `Ω` the whole torus and `L = 2`, the
cube-level size `dCovMod` (the size of (D7) before the fine size replaced it) is `0` and the fine
chosen-cover size `Fluctuation.dcovModE` is `⊤`.  So the fine size is not bounded by an affine
function of the cube-level size. -/
theorem corner_dCovMod_zero_fine_top :
    dCovMod 2 (Set.univ : Set (Torus 2 4)) cornerX = 0 ∧
      Fluctuation.dcovModE (d := 2) (L := 2) (N₁ := 4) (m₁ := 0) (K := 0) 0 0
        (Set.univ : Set (Localization.CTorus 2 2 4 0 0)) (cornerX : Set (Torus 2 4)) = ⊤ :=
  ⟨cornerX_dCovMod, cornerX_fine⟩

end Corner

end Balaban.LargeField.Def7
