module

public import Balaban.LargeField.Operators.Quiet
public import Balaban.LargeField.Characteristic.MeasurableChi
public import Balaban.LargeField.Characteristic.Measurable
public import Balaban.LargeField.Operators.QuietBound
public import Balaban.LargeField.Operators.CompBound

/-!
# Borel measurability of the quiet step kernel (typing of an `LFKernel`)

`measurable_gaussProd`, `measurable_chiNew`, ... and finally `quietKernel_measurable`: for fixed
`h`, the quiet kernel is Borel in `(ψ_{k+1}|_V, I^new_k)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory

section ChiNew

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

theorem measurableSet_setOf_forall {ι : Type*} [Countable ι] {α : Type*} [MeasurableSpace α]
    {Q : ι → α → Prop} (h : ∀ i, MeasurableSet {x | Q i x}) : MeasurableSet {x | ∀ i, Q i x} := by
  have : {x | ∀ i, Q i x} = ⋂ i, {x | Q i x} := by ext; simp
  rw [this]
  exact MeasurableSet.iInter h

theorem measurableSet_setOf_imp {α : Type*} [MeasurableSpace α] {P : Prop} {Q : α → Prop}
    (h : P → MeasurableSet {x | Q x}) : MeasurableSet {x | P → Q x} := by
  by_cases hP : P
  · simpa [hP] using h hP
  · simp [hP]

theorem measurable_msField (j : ℕ) (y : Torus S.d (M * n K * S.L ^ (K - j))) :
    Measurable fun ψ : MultiField S n M K N => ψ j y :=
  (measurable_pi_apply y).comp (measurable_pi_apply j)

theorem measurableSet_psiTilde (Y : Set (BlockPt S n M K)) (δ : ℝ) :
    MeasurableSet {ψ : MultiField S n M K N | PsiTildeMulti ψ Y δ} := by
  unfold PsiTildeMulti
  simp only [Set.ofPred_and]
  refine MeasurableSet.inter ?_ ?_
  · refine measurableSet_setOf_forall fun b => measurableSet_setOf_imp fun _ =>
      measurableSet_setOf_forall fun b' => measurableSet_setOf_imp fun _ =>
        measurableSet_setOf_imp fun _ => measurableSet_setOf_imp fun _ => ?_
    exact measurableSet_lt (((measurable_msField b.1 b.2).sub (measurable_msField b'.1 b'.2)).norm)
      measurable_const
  · refine measurableSet_setOf_forall fun b => measurableSet_setOf_imp fun _ => ?_
    exact measurableSet_lt (((measurable_msField b.1 b.2).norm.pow_const 2).sub_const 1 |>.abs)
      measurable_const

variable {ϱ : ℝ}

theorem measurableSet_chiNewProp (a : LocalHistory S n M K) (k : ℕ)
    (B : GeneratingSet S.d S.L (M * n K) K ϱ) (Zc : Set (Torus S.d (M * n K * S.L ^ K)))
    (δ p0 : ℕ → ℝ) (Cpsi : ℝ) :
    MeasurableSet {p : MultiField S n M K N × MultiField S n M K N |
      ChiNewProp a k B Zc δ p0 Cpsi p.1 p.2} := by
  unfold ChiNewProp
  simp only [Set.ofPred_and]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · refine measurableSet_setOf_forall fun y => measurableSet_setOf_imp fun _ =>
      measurableSet_setOf_imp fun _ => ?_
    exact (measurableSet_psiTilde _ _).preimage measurable_fst
  · refine measurableSet_setOf_forall fun j => measurableSet_setOf_imp fun _ =>
      measurableSet_setOf_imp fun _ => measurableSet_setOf_forall fun y =>
        measurableSet_setOf_imp fun _ => measurableSet_setOf_imp fun _ =>
          measurableSet_setOf_imp fun _ => ?_
    exact (measurableSet_psiTilde _ _).preimage measurable_fst
  · refine measurableSet_setOf_forall fun y => measurableSet_setOf_imp fun _ => ?_
    exact measurableSet_lt ((measurable_msField k y).norm.comp measurable_snd) measurable_const

theorem measurable_chiNew (a : LocalHistory S n M K) (k : ℕ)
    (B : GeneratingSet S.d S.L (M * n K) K ϱ) (Zc : Set (Torus S.d (M * n K * S.L ^ K)))
    (δ p0 : ℕ → ℝ) (Cpsi : ℝ) : Measurable (chiNew (N := N) a k B Zc δ p0 Cpsi) :=
  measurable_charFn (measurableSet_chiNewProp a k B Zc δ p0 Cpsi)

end ChiNew

abbrev QY1 {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M : ℕ} [NeZero M]
    [NeZero S.L] (g : Geo S n R M) (N k : ℕ) : Type :=
  BlockCfg S.d (g.M1 * (g.c * n (k + 1))) S.L (k + 1) k N ×
    BlockCfg S.d (g.M1 * (g.c * n (k + 1))) S.L (k + 1) (k + 1) N

abbrev QMS {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M : ℕ} [NeZero M]
    [NeZero S.L] (g : Geo S n R M) (N k : ℕ) : Type :=
  (m : ℕ) → Blk S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) m → EuclideanSpace ℝ (Fin N)

section Domain

open Balaban.Multiscale in
theorem realFamily_liftMixed {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    (G : GeneratingSet d L N₀ (k + 1) ϱ) {Ω : Finset (Torus d (N₀ * L ^ (k + 1)))}
    (hΩ : IsBlockUnion L N₀ (k + 1) (k + 1) Ω) (hG : G.Ω (k + 1) ⊆ Ω) (h : Fin N → ℝ) :
    RealFamily (fun p : BlockCfg d N₀ L (k + 1) k N × BlockCfg d N₀ L (k + 1) (k + 1) N =>
      liftMixed G hΩ hG p.1.toC p.2.toC (fun i => (h i : ℂ))) h where
  real := by
    intro p x i
    unfold liftMixed BgData.clip
    by_cases hx : x ∈ dataSites G
    · by_cases hxO : x ∈ Ω <;> simp [hx, hxO, mixedLift, blockLift, BlockCfg.toC]
    · simp [hx]
  hconst := by
    intro p x hx i
    rw [liftMixed_h _ _ _ _ _ _ hx]
  Ψc := by
    intro x i
    unfold liftMixed BgData.clip
    by_cases hx : x ∈ dataSites G
    · by_cases hxO : x ∈ Ω
      · simp only [hx, ↓reduceIte, mixedLift, hxO, blockLift, BlockCfg.toC]
        exact Complex.continuous_ofReal.comp
          ((continuous_apply i).comp
            ((continuous_apply (jBlock d L N₀ (k + 1) (k + 1) x)).comp continuous_snd))
      · simp only [hx, ↓reduceIte, mixedLift, hxO, blockLift, BlockCfg.toC]
        exact Complex.continuous_ofReal.comp
          ((continuous_apply i).comp
            ((continuous_apply (jBlock d L N₀ (k + 1) k x)).comp continuous_fst))
    · simp [hx]
      exact continuous_const
  hc := by
    intro x i
    by_cases hx : x ∈ G.Ω 1
    · simp only [liftMixed_h _ _ _ _ _ _ hx]
      exact continuous_const
    · simp only [(liftMixed _ _ _ _ _ _).h_zero x hx]
      exact continuous_const

theorem continuous_bavgL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d L N₀ q : ℕ}
    [NeZero N₀] [NeZero L] (n : ℕ) (y : Blk d L N₀ q n) :
    Continuous fun φ : Site d L N₀ q → E => bavgL d L N₀ q n φ y := by
  unfold bavgL bavg
  exact (continuous_finsetSum _ fun x _ => continuous_apply x).const_smul _

theorem continuous_bondE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d ℓ : ℕ}
    [NeZero ℓ] (X : Finset (Torus d ℓ)) :
    Continuous fun φ : Torus d ℓ → E => bondE X φ := by
  unfold bondE bondEdir bondTerm
  refine continuous_finsetSum _ fun μ _ => continuous_finsetSum _ fun x _ => ?_
  split_ifs
  · fun_prop
  · exact continuous_const

theorem continuous_starBondE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d ℓ : ℕ}
    [NeZero ℓ] (X : Finset (Torus d ℓ)) :
    Continuous fun φ : Torus d ℓ → E => starBondE X φ := by
  classical
  unfold starBondE bondTerm
  refine continuous_finsetSum _ fun μ _ => continuous_finsetSum _ fun x _ => ?_
  split_ifs
  · fun_prop
  · exact continuous_const

theorem continuous_actionG {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d L N₀ q : ℕ}
    [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ q ϱ) (a : ℕ → ℝ) (μ : ℝ) (h : E)
    (X : Finset (Site d L N₀ q)) :
    Continuous fun p : ((m : ℕ) → Blk d L N₀ q m → E) × (Site d L N₀ q → E) =>
      actionG G a μ h X p.1 p.2 := by
  unfold actionG
  refine Continuous.add (Continuous.add ?_ ?_) ?_
  · refine Continuous.const_mul (continuous_finsetSum _ fun n _ =>
      continuous_finsetSum _ fun y _ => Continuous.const_mul ?_ _) _
    have h1 : Continuous fun p : ((m : ℕ) → Blk d L N₀ q m → E) × (Site d L N₀ q → E) => p.1 n y := by
      fun_prop
    have h2 : Continuous fun p : ((m : ℕ) → Blk d L N₀ q m → E) × (Site d L N₀ q → E) =>
        bavgL d L N₀ q n p.2 y := (continuous_bavgL n y).comp continuous_snd
    exact (h1.sub h2).norm.pow 2
  · exact (continuous_bondE X).comp continuous_snd |>.const_mul _
  · refine Continuous.const_mul (continuous_finsetSum _ fun x _ => ?_) _
    fun_prop

theorem continuousOn_barPhi {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    (G : GeneratingSet d L N₀ (k + 1) ϱ) {Y : Type*} [TopologicalSpace Y]
    (D : Y → BgData G N) (a : ℕ → ℝ) (μ c0 : ℝ) {E : Set Y}
    (hΨ : ∀ x i, Continuous fun y => (D y).Ψ x i)
    (hcont : ContinuousOn (fun y => bgFieldC G a μ c0 (D y)) E) :
    ContinuousOn (fun (y : Y) (z : Site d L N₀ (k + 1)) => (WithLp.toLp 2 fun i =>
      (barField G (D y).Ψ (bgFieldC G a μ c0 (D y)) z i).re : EuclideanSpace ℝ (Fin N))) E := by
  refine continuousOn_pi.2 fun z => ?_
  refine (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun i => ?_)
  refine Complex.continuous_re.comp_continuousOn ?_
  by_cases hz : z ∈ G.Ω 1
  · have : (fun y => barField G (D y).Ψ (bgFieldC G a μ c0 (D y)) z i) =
        fun y => bgFieldC G a μ c0 (D y) (⟨z, hz⟩, i) := by
      funext y
      simp [barField, hz]
    rw [this]
    exact (continuous_apply _).comp_continuousOn hcont
  · have : (fun y => barField G (D y).Ψ (bgFieldC G a μ c0 (D y)) z i) =
        fun y => (D y).Ψ z i := by
      funext y
      simp [barField, hz]
    rw [this]
    exact (hΨ z i).continuousOn

theorem continuousOn_expAction {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    (G : GeneratingSet d L N₀ q ϱ) (a : ℕ → ℝ) (μ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (X : Finset (Site d L N₀ q)) (c : ℝ) {Z : Type*} [TopologicalSpace Z] {E : Set Z}
    {ms : Z → (m : ℕ) → Blk d L N₀ q m → EuclideanSpace ℝ (Fin N)}
    {φ : Z → Site d L N₀ q → EuclideanSpace ℝ (Fin N)}
    (hms : Continuous ms) (hφ : ContinuousOn φ E) :
    ContinuousOn (fun z => Real.exp (-(c * (actionG G a μ h X (ms z) (φ z) +
      1 / 4 * starBondE X (φ z))))) E := by
  have hpair : ContinuousOn (fun z => (ms z, φ z)) E := hms.continuousOn.prodMk hφ
  have hact := (continuous_actionG G a μ h X).comp_continuousOn hpair
  have hstar := (continuous_starBondE X).comp_continuousOn hφ
  exact Real.continuous_exp.comp_continuousOn
    ((hact.add (hstar.const_mul (1 / 4))).const_mul c).neg

theorem measurable_indicator_mul {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {E : Set α} (hE : MeasurableSet E) {f : α → ℝ}
    (hf : ContinuousOn f E) :
    Measurable fun r => (open Classical in if r ∈ E then (1 : ℝ) else 0) * f r := by
  classical
  have : (fun r => (if r ∈ E then (1 : ℝ) else 0) * f r) = E.piecewise f (fun _ => 0) := by
    funext r
    by_cases hr : r ∈ E <;> simp [hr]
  rw [this]
  exact ContinuousOn.measurable_piecewise hf continuousOn_const hE

end Domain

section Kernel

theorem measurable_blockCfgOf {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ}
    [NeZero M] [NeZero S.L] {N : ℕ} (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1))
    {q i : ℕ} (hiq : i ≤ q) (hqK : q ≤ K) {Y : Type*} [MeasurableSpace Y]
    {f : Y → BlockAt S n M K i → EuclideanSpace ℝ (Fin N)}
    (hf : ∀ y0, Measurable fun y => f y y0) :
    Measurable fun y => blockCfgOf g hnn hiq hqK (f y) :=
  Measurable.of_eval fun _z => Measurable.of_eval fun j =>
    (EuclideanSpace.proj j).continuous.measurable.comp (hf _)

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1))))
  (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1))) (hk : k + 1 ≤ K)
  (cs : OpConsts) (hrem : ∀ j, Hl.rem j = ∅) (hv : EuclideanSpace ℝ (Fin N))

theorem measurable_psiLevel :
    Measurable fun p : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1) ×
        NewCfg N (locHist Hl M K (k + 1) Zc) k =>
      psiLevel g Hl k hk (subMultiscaleField N (locHist Hl M K (k + 1) Zc) (k + 1)
        (Vblk R (locHist Hl M K (k + 1) Zc) (k + 1)) p.2 p.1) := by
  refine Measurable.of_eval fun m => Measurable.of_eval fun y => ?_
  unfold psiLevel
  by_cases hm : m ≤ k + 1
  · simp only [hm, ↓reduceDIte]
    exact (measurable_subMultiscaleField (N := N) _ m _).comp measurable_swap
  · simp only [hm, ↓reduceDIte]
    exact measurable_const

open Classical in
theorem measurable_domainAction
    (hbg : ∀ q, BgHyp S.d S.L q (minSep S.L g.M1) cs.aw (cs.mu q)) :
    Measurable fun p : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1) ×
        NewCfg N (locHist Hl M K (k + 1) Zc) k =>
      (if InUnionDomainR (locGen g Hl k Zc hZc hk) (bgC1 S.d S.L N) (cs.mu (k + 1))
          (locData g Hl k Zc hZc hk p.1 p.2 hv) then (1 : ℝ) else 0) *
        Real.exp (-mainActionLoc g Hl k Zc hZc hk cs hrem p.1 p.2 hv) := by
  classical
  set G := locGen g Hl k Zc hZc hk with hG
  have hd : 0 < S.d := by
    have := (hbg (k + 1)).hd; omega
  let hΩ : IsBlockUnion S.L (g.M1 * (g.c * n (k + 1))) (k + 1) (k + 1)
      (fineK1 g.M1 g.c (n (k + 1)) S.L k (Hl.step k).Omega) :=
    (isCubeUnion_fineK1 (Hl.step k).Omega).isBlockUnion (le_refl _)
  let hGt : G.Ω (k + 1) ⊆ fineK1 g.M1 g.c (n (k + 1)) S.L k (Hl.step k).Omega :=
    genBoundaryLocal_top_subset (Hl.step k) g.hc (Hl.F.hnn k (by omega))
    Hl.F.ok.two_le_L (g.three_L_le_floor Hl (k - 1)) (Hl.F.stepGeom (by omega)).rad.omega_rho
    (Omega_compl_subset_Zpre' k (Hl.step k) _ _) hZc
  let D : (BlockCfg S.d (g.M1 * (g.c * n (k + 1))) S.L (k + 1) k N ×
      BlockCfg S.d (g.M1 * (g.c * n (k + 1))) S.L (k + 1) (k + 1) N) → BgData G N :=
    fun q => liftMixed G hΩ hGt q.1.toC q.2.toC (fun i => (hv i : ℂ))
  have RF := realFamily_liftMixed G hΩ hGt (fun i => hv i)
  have hE : MeasurableSet {q | InUnionDomainR G (bgC1 S.d S.L N) (cs.mu (k + 1)) (D q)} :=
    measurableSet_domR D hd RF.real RF.hconst RF.Ψc
  obtain ⟨hcont, -⟩ := contOn_bg D (hbg (k + 1)) RF.Ψc RF.hc
  have hphi := continuousOn_barPhi G D cs.aw (cs.mu (k + 1)) (bgC0 S.d S.L N) RF.Ψc hcont
  let Φ : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1) × NewCfg N (locHist Hl M K (k + 1) Zc) k →
      QY1 g N k × QMS g N k := fun p =>
    ((blockCfgOf g Hl.F.hnn (Nat.le_succ k) hk (subVarField N p.2 k),
      blockCfgOf g Hl.F.hnn le_rfl hk (outField N p.1)),
     psiLevel g Hl k hk (subMultiscaleField N (locHist Hl M K (k + 1) Zc) (k + 1)
        (Vblk R (locHist Hl M K (k + 1) Zc) (k + 1)) p.2 p.1))
  have hΦ : Measurable Φ := by
    refine Measurable.prodMk (Measurable.prodMk ?_ ?_) (measurable_psiLevel g Hl k Zc hk)
    · exact measurable_blockCfgOf g Hl.F.hnn (Nat.le_succ k) hk (f := fun p : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1) × NewCfg N (locHist Hl M K (k + 1) Zc) k => subVarField N p.2 k)
        fun y0 => (measurable_subVarField (S := S) (n := n) (M := M) (K := K) (N := N) k y0).comp
          measurable_snd
    · exact measurable_blockCfgOf g Hl.F.hnn le_rfl hk (f := fun p : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1) × NewCfg N (locHist Hl M K (k + 1) Zc) k => outField N p.1)
        fun y0 => (measurable_outField N _ y0).comp measurable_fst
  have hE' : MeasurableSet {r : QY1 g N k × QMS g N k |
      InUnionDomainR G (bgC1 S.d S.L N) (cs.mu (k + 1)) (D r.1)} := hE.preimage measurable_fst
  have hf1 := continuousOn_expAction (histGenLevel g Hl k hk hrem) cs.aw (cs.muAct (k + 1)) hv
    (Xfine g Hl k Zc) (betaCanon S.d S.L (cs.beta (k + 1)) (k + 1) 0)
    (E := {r : QY1 g N k × QMS g N k | InUnionDomainR G (bgC1 S.d S.L N) (cs.mu (k + 1)) (D r.1)})
    (ms := fun r => r.2) (φ := fun r => (fun (z : Site S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1)) =>
      (WithLp.toLp 2 fun i =>
      (barField G (D r.1).Ψ (bgFieldC G cs.aw (cs.mu (k + 1)) (bgC0 S.d S.L N) (D r.1)) z i).re :
      EuclideanSpace ℝ (Fin N))))
    continuous_snd (hphi.comp continuous_fst.continuousOn (fun r hr => hr))
  have : OpensMeasurableSpace (QY1 g N k × QMS g N k) := Prod.opensMeasurableSpace
  have hF := measurable_indicator_mul hE' hf1
  have hcomp := hF.comp hΦ
  convert hcomp using 1
  funext p
  rfl

theorem quietKernel_measurable
    (hbg : ∀ q, BgHyp S.d S.L q (minSep S.L g.M1) cs.aw (cs.mu q)) :
    Measurable fun p : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1) ×
        NewCfg N (locHist Hl M K (k + 1) Zc) k =>
      quietKernel g Hl k Zc hZc hk cs hrem p.1 p.2 hv := by
  unfold quietKernel
  set Y := OutT N R (locHist Hl M K (k + 1) Zc) (k + 1) × NewCfg N (locHist Hl M K (k + 1) Zc) k
    with hY
  have hm1 : Measurable fun p : Y => blockCfgOf g Hl.F.hnn (le_refl k) ((Nat.le_succ k).trans hk)
      (subVarField N p.2 k) :=
    measurable_blockCfgOf g Hl.F.hnn (le_refl k) ((Nat.le_succ k).trans hk) (f := fun p : Y => subVarField N p.2 k)
      fun y0 => (measurable_subVarField (S := S) (n := n) (M := M) (K := K) (N := N) k y0).comp
        measurable_snd
  have hm2 : Measurable fun p : Y => blockCfgOf g Hl.F.hnn (Nat.le_succ k) hk
      (subVarField N p.2 k) :=
    measurable_blockCfgOf g Hl.F.hnn (Nat.le_succ k) hk (f := fun p : Y => subVarField N p.2 k)
      fun y0 => (measurable_subVarField (S := S) (n := n) (M := M) (K := K) (N := N) k y0).comp
        measurable_snd
  have hm3 : Measurable fun p : Y => blockCfgOf g Hl.F.hnn le_rfl hk
      (fun y => cs.z (k + 1) • outField N p.1 y) :=
    measurable_blockCfgOf g Hl.F.hnn le_rfl hk (f := fun p : Y => fun y => cs.z (k + 1) • outField N p.1 y)
      fun y0 => ((measurable_outField N _ y0).comp measurable_fst).const_smul (cs.z (k + 1))
  have hm4 : Measurable fun p : Y => blockCfgOf g Hl.F.hnn le_rfl hk (outField N p.1) :=
    measurable_blockCfgOf g Hl.F.hnn le_rfl hk (f := fun p : Y => outField N p.1)
      fun y0 => (measurable_outField N _ y0).comp measurable_fst
  simp only [mul_assoc]
  refine Measurable.mul ?_ (Measurable.mul ?_ (Measurable.mul ?_ (Measurable.mul ?_
    (Measurable.mul ?_ (Measurable.mul ?_ ?_)))))
  · exact measurable_gaussProd_pair _ k cs
  · exact (measurable_cubeProd (fun y0 => measurable_chiK _ _ _ _ _ _ (hbg k) y0) _).comp hm1
  · exact (measurable_cubeProd (fun y0 => by
      apply measurable_chiPrimeNew (H := hbg (k + 1))) _).comp (hm2.prodMk hm3)
  · exact (measurable_cubeProd (fun y0 => by
      apply measurable_chiPrimeNew (H := hbg (k + 1))) _).comp (hm2.prodMk hm3)
  · exact (measurable_cubeProd (fun y0 => measurable_chiNext _ _ _ _ _ _ _ (hbg (k + 1)) y0) _).comp hm4
  · have hms : Measurable fun p : Y =>
        (subMultiscaleField N (locHist Hl M K (k + 1) Zc) (k + 1)
          (Vblk R (locHist Hl M K (k + 1) Zc) (k + 1)) p.2 p.1,
         subFluctField N (locHist Hl M K (k + 1) Zc) (k + 1) p.2) :=
      Measurable.prodMk
        (Measurable.of_eval fun j => Measurable.of_eval fun y =>
          (measurable_subMultiscaleField (N := N) _ j y).comp measurable_swap)
        (Measurable.of_eval fun j => Measurable.of_eval fun y =>
          (measurable_subFluctField j y).comp measurable_snd)
    exact (measurable_chiNew _ _ _ _ _ _ _).comp hms
  · exact measurable_domainAction g Hl k Zc hZc hk cs hrem hv hbg

end Kernel

end Balaban.LargeField
