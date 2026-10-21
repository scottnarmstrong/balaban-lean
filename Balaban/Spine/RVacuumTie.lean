/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RStep

/-!
# The vacuum tie of a record, from the estimate of `b⁰_k`

A record of `ℛ^pre_k` carries the scale-indexed vacuum flow `E_j` (`PreRec.Ev`). `VacuumTied` asks
that the vacuum constants of its step data be those of the flow (`StepData.VacuumTie`). Retying a
record keeps the kernels, the boundary factors `b_k` and everything that reads only these, and
sets the vacuum constants to `E_k`, `E_k + δ″_k`, `E_k + δ‴_k` and `b⁰_k := b_k + (vacuum term)`.
The one estimate that this needs is the bound of `b⁰_k` by `(C_b log β_k + C_b B₀)|Z_{k+1} ∖ Z_k|_{k+1}`
(`VacuumB0Bound`, `StepData.b0_bound`); it is a consequence of the flow bound `|E_j| ≤ C_b (log β_j + 1)`
together with the volume and offset estimates of P4 (2.1), (2.41), (2.63), and is the content of
`RVacuumB0Input`.

* `StepData.retie`: the step data with the vacuum constants of a flow;
* `VacuumB0Bound`, `RVacuumB0Input`: the estimate of `b⁰_k` for the retied data;
* `rVacuumInput_of_b0`: `RVacuumInput` from `RVacuumB0Input`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6v2 Balaban.Multiscale RegionHistory

section Retie

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts}
  {κs : ℕ → LocalHistory S n M K → ℝ}

/-- **The estimate of `b⁰_k` for the vacuum constants of a flow** (`StepData.b0_bound`; P4 (2.1),
(2.41), (2.63)): with `E_k`, `E″_k = E_k + δ″_k`, `E‴_k = E_k + δ‴_k`, the boundary factor plus the
vacuum term of the creating step is bounded by `(C_b log β_k + C_b B₀)|Z_{k+1} ∖ Z_k|_{k+1}`. -/
def VacuumB0Bound (SD : StepData k0 geo cs N κs) (E dpp dppp : ℕ → ℝ) : Prop :=
  ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (k : ℕ)
    (Z' : H.Comp (k + 1)) o x hv (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) →
    ChiNewAt geo cs H k Z' o x →
    ‖(SD.ker k (H.localHistory M K (k + 1) Z')).b o x hv g +
        (stepVacuumTerm (H.localHistory M K (k + 1) Z') k (E k) (E k + dpp k) (E k + dppp k) : ℂ)‖ ≤
      (cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) *
        volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
          z ∉ (H.localHistory M K (k + 1) Z').Z k}

/-- **The step data with the vacuum constants of a flow**: the kernels and boundary factors are
those of `SD`, the vacuum constants are `E_k`, `E_k + δ″_k`, `E_k + δ‴_k`, and
`b⁰_k = b_k + (vacuum term)`. The estimate of `b⁰_k` is `VacuumB0Bound`. -/
noncomputable def _root_.Balaban.LargeField.StepData.retie (SD : StepData k0 geo cs N κs) (E dpp dppp : ℕ → ℝ)
    (hb : VacuumB0Bound SD E dpp dppp) : StepData k0 geo cs N κs :=
  { SD with
    vacE := fun k _ => E k
    vacEpp := fun k _ => E k + dpp k
    vacEppp := fun k _ => E k + dppp k
    b0 := fun k a o x hv g => (SD.ker k a).b o x hv g +
      (stepVacuumTerm a k (E k) (E k + dpp k) (E k + dppp k) : ℂ)
    b_vac := fun _ _ _ _ _ _ => by ring
    b0_bound := hb }

theorem _root_.Balaban.LargeField.StepData.retie_ker (SD : StepData k0 geo cs N κs) (E dpp dppp : ℕ → ℝ)
    (hb : VacuumB0Bound SD E dpp dppp) : (SD.retie E dpp dppp hb).ker = SD.ker := rfl

theorem _root_.Balaban.LargeField.StepData.retie_tie (SD : StepData k0 geo cs N κs) (E dpp dppp : ℕ → ℝ)
    (hb : VacuumB0Bound SD E dpp dppp) :
    (SD.retie E dpp dppp hb).VacuumTie Set.univ E dpp dppp where
  E_eq _ _ _ := rfl
  Epp_eq _ _ _ := rfl
  Eppp_eq _ _ _ := rfl

end Retie

section Ops

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts}
  {κs κ : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  {SD SD' : StepData k0 geo cs N κs} (KD : KeptData k0 geo cs N κ lamHat)
  {H : RegionHistory S n R k0 K}

/-- The pre-operator reads the step data only through the kernels `ker`. -/
theorem preOp_congr (hker : SD'.ker = SD.ker) (hH : H.Admissible) {k : ℕ} (hK : k + 1 ≤ K)
    (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k) :
    preOp geo cs SD' hH hK Z' sub = preOp geo cs SD hH hK Z' sub := by
  simp only [preOp, hker]

/-- The localized operators read the step data only through the kernels `ker`. -/
theorem locOp_congr (hker : SD'.ker = SD.ker) (hH : H.Admissible)
    (lab : ∀ k, H.Comp k → Fin 5) (k : ℕ) (hk : k ≤ K) (Z : H.Comp k) :
    locOp geo cs SD' KD hH lab k hk Z = locOp geo cs SD KD hH lab k hk Z := by
  induction k with
  | zero => exact ((H.F.isEmpty_comp_zero.false Z).elim)
  | succ k ih =>
    by_cases hc : IsKept H (k + 1) Z
    · rw [locOp_kept _ _ _ _ hk hc, locOp_kept _ _ _ _ hk hc]
    · rw [locOp_level _ _ _ _ hk hc, locOp_level _ _ _ _ hk hc, preOp_congr hker]
      congr 1
      funext Y _
      exact ih _ Y

/-- The top-level pre-operators read the step data only through the kernels `ker`. -/
theorem preOpTop_congr (hker : SD'.ker = SD.ker) (A : LabHist S n R k0 K) (k : ℕ) (hk : k ≤ K)
    (Z : A.H.Comp k) :
    preOpTop geo cs SD' KD A k hk Z = preOpTop geo cs SD KD A k hk Z := by
  cases k with
  | zero => exact ((A.H.F.isEmpty_comp_zero.false Z).elim)
  | succ k =>
    simp only [preOpTop]
    rw [preOp_congr hker]
    congr 1
    funext Y _
    exact locOp_congr KD hker _ _ _ _ _

end Ops

section Rep

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}

/-- The representation with other step data: the history, the kept data and the boundary terms
are those of `rep`. -/
def _root_.Balaban.LargeField.Def7.Rep.withSD (rep : Rep S n R k0 K M N geo cs P k)
    (SD' : StepData k0 geo cs N (kappaStepLoc (K := K) S P M)) : Rep S n R k0 K M N geo cs P k :=
  { rep with SD := SD' }

theorem withSD_SD (rep : Rep S n R k0 K M N geo cs P k)
    (SD' : StepData k0 geo cs N (kappaStepLoc (K := K) S P M)) : (rep.withSD SD').SD = SD' := rfl

theorem withSD_KD (rep : Rep S n R k0 K M N geo cs P k)
    (SD' : StepData k0 geo cs N (kappaStepLoc (K := K) S P M)) : (rep.withSD SD').KD = rep.KD := rfl

theorem withSD_κK (rep : Rep S n R k0 K M N geo cs P k)
    (SD' : StepData k0 geo cs N (kappaStepLoc (K := K) S P M)) : (rep.withSD SD').κK = rep.κK := rfl

theorem withSD_hist (rep : Rep S n R k0 K M N geo cs P k)
    (SD' : StepData k0 geo cs N (kappaStepLoc (K := K) S P M)) : (rep.withSD SD').hist = rep.hist :=
  rfl

theorem d5Bound_withSD {rep : Rep S n R k0 K M N geo cs P k}
    {SD' : StepData k0 geo cs N (kappaStepLoc (K := K) S P M)} (hker : SD'.ker = rep.SD.ker)
    {top : ℕ} {hkK : k ≤ K} (h : D5Bound top hkK rep) : D5Bound top hkK (rep.withSD SD') := by
  intro A hA j hj
  obtain ⟨h1, h2⟩ := h A hA j hj
  refine ⟨fun hjt c hc => ?_, fun c => ?_⟩
  · have := h1 hjt c hc
    show PkgBound _ _ (locOp geo cs SD' rep.KD A.adm _ _ _ c) (rep.kappaH A j c)
    rw [locOp_congr rep.KD hker]
    exact this
  · have := h2 c
    show PkgBound _ _ (preOpTop geo cs SD' rep.KD A _ _ c) (rep.kappaPreH A j c)
    rw [preOpTop_congr rep.KD hker]
    exact this

theorem integrand2_withSD {ι : Type} [Fintype ι] (a : ι → LocalHistory S n M K)
    (Pk : ∀ i, OpPkg N R (a i) k) (car : ι → Set (Torus S.d (M * n K * S.L ^ K)))
    {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (rep : Rep S n R k0 K M N geo cs P k)
    (SD' : StepData k0 geo cs N (kappaStepLoc (K := K) S P M))
    (A : LabHist S n R k0 K) (Z : Set (Torus S.d (n k)))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) :
    integrand2 a Pk car C vc (rep.withSD SD') A Z ψk hv g = integrand2 a Pk car C vc rep A Z ψk hv g :=
  rfl

theorem d1PreForm2_withSD {rep : Rep S n R k0 K M N geo cs P k}
    {SD' : StepData k0 geo cs N (kappaStepLoc (K := K) S P M)} (hker : SD'.ker = rep.SD.ker)
    {m₁ : ℕ} {ϱ : ℝ} {C : SFCtx S n R M K N k m₁ ϱ} {vc : CorrCoef S.d}
    {hv : EuclideanSpace ℝ (Fin N)}
    {ρ : (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) → (GIdx S n M K N → ℂ) → ℂ}
    (h : D1PreForm2 C vc rep hv ρ) : D1PreForm2 C vc (rep.withSD SD') hv ρ := by
  intro ψk g hg
  obtain ⟨h1, h2⟩ := h ψk g hg
  have hop : ∀ (A : LabHist S n R k0 K) (j : ℕ) (hj : j ≤ K),
      preOpTop geo cs SD' rep.KD A j hj = preOpTop geo cs rep.SD rep.KD A j hj := by
    intro A j hj
    funext Z
    exact preOpTop_congr rep.KD hker A j hj Z
  refine ⟨fun A hA => ?_, ?_⟩
  · have := h1 A hA
    unfold PreConv2 at this ⊢
    simp only [integrand2_withSD, withSD_SD, withSD_KD, withSD_κK]
    rw [hop A k C.hkK]
    exact this
  · rw [h2]
    unfold preTerm2
    simp only [integrand2_withSD, withSD_SD, withSD_KD, withSD_κK, withSD_hist]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [hop A k C.hkK]

theorem d7Bdry2_withSD {rep : Rep S n R k0 K M N geo cs P k}
    {SD' : StepData k0 geo cs N (kappaStepLoc (K := K) S P M)}
    {m₀ m₁ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {hnn : ∀ i, i < K → n i = S.L * n (i + 1)}
    {hkK : k ≤ K} {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))} {aw μs ε ε1 νs : ℕ → ℝ}
    {fac rate : ℝ} {hv : EuclideanSpace ℝ (Fin N)} {rH : ℝ}
    (h : D7Bdry2 Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv rH) :
    D7Bdry2 Fr hnn hkK (rep.withSD SD') Zof aw μs ε ε1 νs fac rate hv rH :=
  { h with }

end Rep

section Record

variable {d N : ℕ} {T : Typing} {P6 : Def6.Consts} {C7 : Consts7} {PB : BudgetConsts}
  {cs₀ : OpConsts} {M1 c : ℕ} {rH ϱ β ν : ℝ} {h : EuclideanSpace ℝ (Fin N)} {kf k r : ℕ}
  [NeZero T.M] [NeZero T.L] {ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k]} {νk : ℝ}

/-- **The estimate of `b⁰_k` for the flow of a record, with offsets** `δ″, δ‴` (chosen per torus, not
depending on `E_k`): `VacuumB0Bound` of the step data of every torus. -/
def RecB0Bound (rec : PreRec d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k r ρ νk) : Prop :=
  ∀ (nK : ℕ) [NeZero nK], ∃ dpp dppp : ℕ → ℝ, VacuumB0Bound (rec.F.lf nK).SD rec.Ev dpp dppp

/-- **The retied record**: the step data of every torus are replaced by `StepData.retie` with the
flow `rec.Ev`; kernels, boundary factors, kept data and boundary terms are those of `rec`. -/
noncomputable def PreRec.retie (rec : PreRec d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k r ρ νk)
    (hb : RecB0Bound rec) :
    PreRec d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k r ρ νk :=
  have hker : ∀ (nK : ℕ) [NeZero nK], ((rec.F.lf nK).SD.retie rec.Ev (hb nK).choose
      (hb nK).choose_spec.choose (hb nK).choose_spec.choose_spec).ker = (rec.F.lf nK).SD.ker :=
    fun _ _ => rfl
  { rec with
    F := ⟨rec.F.sf, fun nK _ => (rec.F.lf nK).withSD ((rec.F.lf nK).SD.retie rec.Ev (hb nK).choose
      (hb nK).choose_spec.choose (hb nK).choose_spec.choose_spec)⟩
    pre :=
      { coh := rec.pre.coh
        field := rec.pre.field
        complete := fun nK _ => rec.pre.complete nK
        form := fun nK _ => d1PreForm2_withSD (hker nK) (rec.pre.form nK)
        corr := rec.pre.corr
        sfData := rec.pre.sfData
        pin := fun nK _ => rec.pre.pin nK
        opBound := fun nK _ => d5Bound_withSD (hker nK) (rec.pre.opBound nK)
        budget := fun nK _ => rec.pre.budget nK
        bdry := fun nK _ => d7Bdry2_withSD (rec.pre.bdry nK)
        coherent := rec.pre.coherent
        coeff := rec.pre.coeff }
    coh := rec.coh
    vac := rec.vac
    vacTie := fun nK _ => ⟨(hb nK).choose, (hb nK).choose_spec.choose,
      StepData.retie_tie _ _ _ _ _⟩ }

end Record

section Input

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- **A4-2v′, the estimate of `b⁰_k` (P4 (2.1), (2.41), (2.63); LFR proof of Theorem IV.1.1; R5, R5′).**
For `1 ≤ k ≤ k₀`, every member of `ℛ^pre_k` (I.2 up to `k`, torus coherent) with its vacuum flow
`E_j`, `|E_j| ≤ C_b (log β_j + 1)` (`PreRec.vac`), has offsets `δ″_j, δ‴_j` (the same on every torus)
for which the boundary factor plus the vacuum term of the creating step is bounded by
`(C_b log β_k + C_b B₀)|Z_{k+1} ∖ Z_k|_{k+1}` (`RecB0Bound`). The bound of the vacuum term uses the
flow bound, the offsets `δ″_k = -½ N L^{-d} log (c/2π) + ½ N log β_k`, `δ‴_k = δ″_k - e(N, p₁) - ½ N log 2π`
(`O(log β_k)`), and the volumes of the three vacuum regions against `|Z_{k+1} ∖ Z_k|_{k+1}`
(`stepVacuumVolume_eq_add_excess`). It is proved (`rVacuumB0Input`, `Spine/RVacuumRetieBound.lean`) from
the vacuum tie `PreRec.vacTie`: the flow constant is the vacuum constant of the creating step, so the
retie changes nothing. -/
def RVacuumB0Input : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → k ≤ kZero d (T κ c₉).L β ν →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ),
  ∀ rec : PreRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k k ρ νk,
    RecB0Bound rec

/-- **`RVacuumInput` from the estimate of `b⁰_k`**: the record with the step data retied to its flow
(`PreRec.retie`) has the same density and is `VacuumTied`. -/
theorem rVacuumInput_of_b0 (hb : RVacuumB0Input d N T P6 C7 PB cs₀ M1 c rH ϱ) :
    RVacuumInput d N T P6 C7 PB cs₀ M1 c rH ϱ := by
  intro κ hκ c₉ hc₉
  obtain ⟨β₀, hβ₀⟩ := hb κ hκ c₉ hc₉
  refine ⟨β₀, fun β hβ ν hν hνL h hh kf hkf _ _ k hk1 hk ρ νk rec => ?_⟩
  have hr := hβ₀ β hβ ν hν hνL h hh kf hkf k hk1 hk ρ νk rec
  exact ⟨rec.retie hr, fun nK _ => ⟨_, _, StepData.retie_tie _ _ _ _ _⟩⟩

end Input

end Balaban.RootFSpine
