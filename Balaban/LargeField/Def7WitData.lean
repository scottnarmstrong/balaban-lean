module

public import Balaban.LargeField.Def7Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Def-7 witness, part 2: the zero step and kept data, operators with zero kernels

* `zeroKer`: the large-field kernel `(K, b) = (0, 0)`.
* `zeroStepData`: step data (S0)-(S2) with zero kernels for a horizon `K ≤ 1` (the only step is
  `0 → 1`, which is never quiet: `not_isQuiet_zero`, Lemma II.7.2 (c)) and `C_b = 0`;
  `zeroKeptData`: kept data (S3) with zero kernels, `C_dec ≡ 5`, `γ = A'_3 λ̂^{p_R} + log 5`.
* `locOp_K_zero`, `preOpTop_K_zero`: with zero data every localized operator has a zero kernel;
  `kerBound_of_K_zero`: such an operator satisfies (1.26) with every exponent.
* `gConv_of_K_zero`: the integral of the global operator of a family of such operators converges
  absolutely for every integrand (it vanishes unless the family is empty, where the measure is a
  Dirac mass).
* `not_ripe_one`: under the conditions of LF-2 no component of `Z^pre_1` is ripe.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Def7

open MeasureTheory Balaban RegionHistory

/-- The zero large-field kernel. -/
def zeroKer (O X H ι : Type*) [MeasurableSpace O] [MeasurableSpace X] [Fintype ι] :
    LFKernel O X H ι where
  K := fun _ _ _ => 0
  b := fun _ _ _ _ => 0
  K_nonneg := fun _ _ _ => le_rfl
  measurable_K := fun _ => measurable_const
  measurable_b := fun _ _ => measurable_const
  analytic_b := fun _ _ _ => analyticOnNhd_const
  real_b := fun _ _ _ _ _ _ => by simp

section Data

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- **The step `0 → 1` is never quiet** (Lemma II.7.2 (c)): every component `Z'` of `Z^pre_1`
contains a new cube (it has no old parts). -/
theorem not_isQuiet_zero (H : RegionHistory S n R k0 K) (hK : 1 ≤ K) (Z' : H.Comp 1) :
    ¬ IsQuiet (H.locRH 1 Z') 0 Z'.1 := by
  intro hq
  have hmem := locComp_mem H hK Z'
  have hs : 1 ≤ ((H.locRH 1 Z').parts 0 ⟨Z'.1, hmem⟩).card +
      (Z'.1 ∩ (H.locRH 1 Z').newCubes (0 + 1)).card :=
    (H.locRH 1 Z').seed_pos (show 0 < K by omega) ⟨Z'.1, hmem⟩
  have hp : ((H.locRH 1 Z').parts 0 ⟨Z'.1, hmem⟩).card = 0 := by
    have := (H.locRH 1 Z').F.isEmpty_comp_zero
    rw [Finset.card_eq_zero]
    exact Finset.eq_empty_of_isEmpty _
  have hq' : (Z'.1 ∩ (H.locRH 1 Z').newCubes (0 + 1)).card = 0 := by
    unfold IsQuiet at hq
    rw [hq]; rfl
  omega

variable (geo : Geo S n R M) (cs : OpConsts)

/-- The empty Gaussian witness. -/
def emptyWit (a : LocalHistory S n M K) (k : ℕ) : GaussWit N R a k where
  W := Empty
  F := fun w => w.elim
  Kt := fun w => w.elim

theorem sum_emptyWit {a : LocalHistory S n M K} {k : ℕ} {β : Type*} [AddCommMonoid β]
    (f : (emptyWit (N := N) (R := R) a k).W → β) : ∑ w, f w = 0 := by
  have : IsEmpty (emptyWit (N := N) (R := R) a k).W := inferInstanceAs (IsEmpty Empty)
  exact Fintype.sum_empty f

/-- **Zero step data** for a horizon `K ≤ 1` and `C_b = 0`: (S0)-(S2) hold with every exponent. -/
noncomputable def zeroStepData (hK : K ≤ 1) (hCb : cs.Cb = 0) (κs : ℕ → LocalHistory S n M K → ℝ) :
    StepData k0 geo cs N κs where
  ker := fun _ _ => zeroKer _ _ _ _
  wit := fun k a => emptyWit a k
  b_supp := fun _ _ _ _ _ _ _ _ => rfl
  rot_K := fun _ _ _ _ _ _ => rfl
  rot_b := fun _ _ _ _ _ _ _ => rfl
  euclid_K := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  euclid_b := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  b_bound := fun _ _ _ _ _ _ _ _ _ _ => by
    simp [zeroKer, hCb]
  quiet := fun H _ k hk Z' hq => by
    have hk0 : k = 0 := by omega
    subst hk0
    exact absurd hq (not_isQuiet_zero H (by omega) Z')
  dom := fun _ _ _ _ _ _ _ _ => rfl
  gauss := fun _ _ _ _ => by
    refine ⟨fun w => w.elim, fun w => w.elim, fun w => w.elim, fun w => w.elim,
      fun _ _ _ => by rw [sum_emptyWit, mul_zero]; rfl, fun w => w.elim,
      fun w => w.elim, fun w => w.elim, fun _ _ _ _ => by rw [sum_emptyWit]; exact zero_le⟩

/-- **Zero kept data**: kept kernels `0`, `C_dec ≡ 5`, `γ_k = A'_3 λ̂_k^{p_R} + log 5`. -/
noncomputable def zeroKeptData (κ : ℕ → LocalHistory S n M K → ℝ) (lamHat : ℕ → ℝ) :
    KeptData k0 geo cs N κ lamHat where
  datum := fun _ _ _ =>
    { Ikeep := Set.univ
      contains := fun _ _ => Set.mem_univ _
      ker := zeroKer _ _ _ _ }
  Cdec := fun _ => 5
  gam := fun k _ => S.A3' * lamHat k ^ S.pR + Real.log 5
  one_le_Cdec := fun _ => by norm_num
  sum_inv_Cdec := by simp
  gam_ge := fun _ _ => by simp
  b_supp := fun _ _ _ _ _ _ _ _ _ => rfl
  rot_K := fun _ _ _ _ _ _ _ => rfl
  rot_b := fun _ _ _ _ _ _ _ _ => rfl
  euclid_I := fun _ _ _ _ _ _ _ _ => by simp
  euclid_K := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  euclid_b := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  bound := fun _ _ _ _ _ _ _ _ =>
    ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => by simp [LFKernel.absW, zeroKer]⟩

/-- A kernel with `K = 0` satisfies (1.26) with every exponent. -/
theorem kerBound_of_K_zero (a : LocalHistory S n M K) (k : ℕ) {A : Set (InternalVars a k)}
    (T : LFKernel (OutT N R a k) (SubCfg N a k A) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N))
    (hT : ∀ o x h, T.K o x h = 0) (κ : ℝ) : KerBound a k T κ := by
  intro hv g _ par
  simp [LFKernel.absW, hT]

variable {κs κ : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  {SD : StepData k0 geo cs N κs} {KD : KeptData k0 geo cs N κ lamHat}

/-- With zero step and kept kernels, every localized operator has a zero kernel. -/
theorem locOp_K_zero (hSD : ∀ k a o x hv, (SD.ker k a).K o x hv = 0)
    (hKD : ∀ k a ϰ o x hv, (KD.datum k a ϰ).ker.K o x hv = 0) {H : RegionHistory S n R k0 K}
    (hH : H.Admissible) (lab : ∀ k, H.Comp k → Fin 5) :
    ∀ (k : ℕ) (hk : k ≤ K) (Z : H.Comp k) o x hv,
      (locOp geo cs SD KD hH lab k hk Z).T.K o x hv = 0
  | 0, _, Z, _, _, _ => (H.F.isEmpty_comp_zero.false Z).elim
  | k + 1, hk, Z', o, x, hv => by
    by_cases hc : IsKept H (k + 1) Z'
    · have e := locOp_kept geo cs SD KD (lab := lab) (hH := hH) hk hc
      have key : ∀ P : OpPkg N R (H.localHistory M K (k + 1) Z') (k + 1),
          P = keptOp geo cs KD hH Z' hc.1 hc.2.1 hc.2.2 (lab (k + 1) Z') →
          ∀ x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) P.A, P.T.K o x hv = 0 := by
        intro P hP
        subst hP
        intro x
        exact hKD _ _ _ _ _ _
      exact key _ e x
    · have e := locOp_level geo cs SD KD (lab := lab) (hH := hH) hk hc
      have key : ∀ P : OpPkg N R (H.localHistory M K (k + 1) Z') (k + 1),
          P = preOp geo cs SD hH hk Z' (fun Y _ => locOp geo cs SD KD hH lab k (by omega) Y) →
          ∀ x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) P.A, P.T.K o x hv = 0 := by
        intro P hP
        subst hP
        intro x
        change (SD.ker k (H.localHistory M K (k + 1) Z')).K o _ hv * _ = 0
        rw [hSD, zero_mul]
      exact key _ e x

/-- With zero step kernels, every pre-`R` operator has a zero kernel. -/
theorem preOpTop_K_zero (hSD : ∀ k a o x hv, (SD.ker k a).K o x hv = 0)
    (A : LabHist S n R k0 K) :
    ∀ (k : ℕ) (hk : k ≤ K) (Z : A.H.Comp k) o x hv,
      (preOpTop geo cs SD KD A k hk Z).T.K o x hv = 0
  | 0, _, Z, _, _, _ => (A.H.F.isEmpty_comp_zero.false Z).elim
  | k + 1, hk, Z', o, x, hv => by
    change (SD.ker k (A.H.localHistory M K (k + 1) Z')).K o _ hv * _ = 0
    rw [hSD, zero_mul]

end Data

section Conv

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {ι : Type} [Fintype ι] (a : ι → LocalHistory S n M K) (k : ℕ)
  (P : ∀ i, OpPkg N R (a i) k)

/-- The integral of the global operator of a family of operators with zero kernels converges
absolutely for every integrand: the product kernel vanishes unless the family is empty, and for
the empty family the reference measure is a Dirac mass. -/
theorem gConv_of_K_zero (hP : ∀ i o x hv, (P i).T.K o x hv = 0)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (F : GCfg a k P → ℂ) : GConv a k P ψk hv g F := by
  unfold GConv
  rcases isEmpty_or_nonempty ι with hι | hne
  · have hm : gMeasure a k P = Measure.dirac (isEmptyElim : GCfg a k P) := by
      unfold gMeasure; exact Measure.pi_of_empty _ _
    rw [hm]
    have hc : (fun x => gWeight a k P ψk hv g x * F x) =
        fun _ => gWeight a k P ψk hv g isEmptyElim * F isEmptyElim := by
      funext x
      have : x = (isEmptyElim : GCfg a k P) := funext fun i => isEmptyElim i
      rw [this]
    rw [hc]
    exact integrable_const _
  · obtain ⟨i₀⟩ := hne
    have hz : (fun x => gWeight a k P ψk hv g x * F x) = fun _ => 0 := by
      funext x
      have : gWeight a k P ψk hv g x = 0 := by
        unfold gWeight
        refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
        simp [LFKernel.w, hP]
      rw [this, zero_mul]
    rw [hz]
    exact integrable_zero _ _ _

end Conv

/-- **No component of `Z^pre_1` is ripe** under the conditions of LF-2: it has no old parts and at
least one new cube, so its window state is a restart at scale `1`, and `t^* ≥ 1 + n_q(1) > 1`. -/
theorem not_ripe_one {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
    (G : S.Good) (H : RegionHistory S n R k0 K) (hK : 1 ≤ K) (c : H.Comp 1) :
    ¬ S.Ripe 1 (H.bk 1 c) := by
  classical
  rintro ⟨⟨q, ν, Ms, hst⟩, ht⟩
  have hparts : H.parts 0 c = ∅ := by
    have := H.F.isEmpty_comp_zero
    exact Finset.eq_empty_of_isEmpty _
  have hr : 1 ≤ (c.1 ∩ H.newCubes (0 + 1)).card := by
    have := H.seed_pos (show 0 < K by omega) c
    rw [hparts, Finset.card_empty] at this
    omega
  have hb : H.bk 1 c = S.nextBook 1 (H.parts 0 c) (fun c => S.postBook k0 0 (H.bk 0 c))
      (c.1 ∩ H.newCubes 1).card (H.spine 1 c) := rfl
  have hr' : 1 ≤ (c.1 ∩ H.newCubes 1).card := hr
  have hst' : (H.bk 1 c).st = WState.restart 1 ((H.spine 1 c).length = 0) := by
    rw [hb]
    simp only [Setting.nextBook, Setting.nextState, hr', ↓reduceIte]
  rw [hst'] at hst
  unfold WState.restart at hst
  split_ifs at hst with hpt
  · -- the restarted state is `Active(1, 1, ∅)`
    have hq : (H.bk 1 c).q = 1 := by
      unfold Book.q
      rw [hst']
      unfold WState.restart
      simp [hpt]
    have hlt := G.n2_lt_nq 1
    have : 1 + S.nq 1 ≤ S.tStar (H.bk 1 c) := by
      unfold Setting.tStar
      rw [hq]
      exact le_max_left _ _
    omega

end Balaban.LargeField.Def7
