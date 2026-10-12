module

public import Balaban.Background.Theorem73
public import Balaban.Fluctuation.CriticalPointGauss
public import Balaban.SmallField.Def6Terms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Lemma 2.2 (b)--(d): the critical point (FLUCTUATION.md §2.2)

Setting.  Whole-lattice generating sets `G` (level `n = k`) and `G'` (level `n + 1`) on the common
fine torus, `IsLevel` (`levelGS`, `isLevel_levelGS`); weights `a = compWeight L a₁`; the data of
level `n + 1` is the pair `(θ, h) = (D'.Ψ, D'.h)`.

* `Jbg`, `Jinf`: `J_k(θ, ψ)` with the background field and as the minimum over the sphere;
* `criticalPoint_real` (b): `ψ^{(k)} = composeData …` is real, in the real domain, equals
  `Ψ(θ, φ_{k+1}(θ))`, is the unique global minimiser of `J_k(θ, ·)` with
  `J_k(θ, ψ^{(k)}) = A_{k+1}(θ, φ_{k+1}(θ))`, and `φ_k(ψ^{(k)}) = φ_{k+1}`, `α_k(ψ^{(k)}) = α_{k+1}`;
* `criticalPoint_complex` (c): the same identities for complex data (BG Theorem 6.1);
* `criticalPoint_real_nuFree`, `action_mass_split` (d): the `ν`-free convention.

All actions are the Background actions (fine units); the `η`-unit actions of FLUCTUATION are
`L^{-k(d-2)}` times these (FLUCTUATION §1.1), a common factor.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

section Level

variable {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'}

/-- **A whole-lattice generating set of level `n`**: `Ω₁` is the whole torus and every site lies in
layer `n` (`Ω_1 = … = Ω_n = 𝕋`, `Ω_{n+1} = ∅`).  This is the shape of the single-scale sets
`𝔹_n` of the class (`levelGS n`, `GeneratingSet.single`). -/
def IsLevel (G : GeneratingSet d L N₀ K ϱ) (n : ℕ) : Prop :=
  ∀ x, x ∈ G.Ω 1 ∧ G.layerIndex x = n

theorem IsLevel.bounds {n : ℕ} (h : IsLevel G n) : 1 ≤ n ∧ n ≤ K := by
  obtain ⟨h1, h2, -⟩ := G.layerIndex_spec (h 0).1
  rw [(h 0).2] at h1 h2
  exact ⟨h1, h2⟩

theorem IsLevel.Ω_one {n : ℕ} (h : IsLevel G n) : G.Ω 1 = Finset.univ :=
  Finset.eq_univ_of_forall fun x => (h x).1

theorem IsLevel.mem_layer {n : ℕ} (h : IsLevel G n) (x : Torus d (N₀ * L ^ K)) :
    x ∈ G.layer n := by
  obtain ⟨-, -, h3⟩ := G.layerIndex_spec (h x).1
  rw [(h x).2] at h3
  exact h3

theorem IsLevel.sum_Ω {n : ℕ} (h : IsLevel G n) (F : Torus d (N₀ * L ^ K) → ℝ) :
    ∑ x : G.Ω 1, F x = ∑ x, F x := by
  rw [Finset.sum_coe_sort (G.Ω 1) F, h.Ω_one]

theorem IsLevel.precedes {n : ℕ} (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) : Precedes G G' := by
  intro i hi hiK x hx
  have hxl := hG.mem_layer x
  have hxl' := hG'.mem_layer x
  rw [GeneratingSet.mem_layer] at hxl hxl'
  by_cases hin : i ≤ n
  · exact G'.Ω_antitone hi (by omega) (by omega) hxl'.1
  · exfalso
    exact hxl.2 (G.Ω_antitone (by omega) (by omega) (by omega) hx)

/-- The level term `½ ∑_x a_n L^{-2n} |Ψ - Q_n φ|²` of the action. -/
noncomputable def levelTerm (G : GeneratingSet d L N₀ K ϱ) (a : ℕ → ℝ) {N : ℕ} (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) : ℝ :=
  (1 / 2) * ∑ x : G.Ω 1, (a (G.layerIndex (x : Torus d (N₀ * L ^ K))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ K))) ^ 2) *
      ∑ i, ‖D.Ψ x i - blockAvg G φ x i‖ ^ 2

/-- The gradient and mass terms of the action. -/
noncomputable def restTerm (G : GeneratingSet d L N₀ K ϱ) (ν : ℝ) {N : ℕ} (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) : ℝ :=
  (1 / 2) * ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, ‖barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i‖ ^ 2 else 0) +
  ν / 2 * ∑ x : G.Ω 1, ∑ i, ‖φ (x, i) - D.h x i‖ ^ 2

theorem action_eq_level_add_rest (a : ℕ → ℝ) (ν : ℝ) {N : ℕ} (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) :
    action G a ν D φ = levelTerm G a D φ + restTerm G ν D φ := by
  unfold action levelTerm restTerm
  ring

theorem levelTerm_eq {n : ℕ} (hG : IsLevel G n) (a : ℕ → ℝ) {N : ℕ} (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) :
    levelTerm G a D φ = (1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) * ∑ x, ∑ i,
      ‖D.Ψ x i - blockMean G n (fun y => svec G φ y i) x‖ ^ 2 := by
  unfold levelTerm
  rw [mul_assoc]
  congr 1
  have := hG.sum_Ω (fun x => (a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2) *
      ∑ i, ‖D.Ψ x i - blockAvg G φ x i‖ ^ 2)
  rw [show (∑ x : G.Ω 1, (a (G.layerIndex (x : Torus d (N₀ * L ^ K))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ K))) ^ 2) *
      ∑ i, ‖D.Ψ x i - blockAvg G φ x i‖ ^ 2) = _ from this]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [(hG x).2]
  have hb : ∀ i, blockAvg G φ x i = blockMean G n (fun y => svec G φ y i) x := fun i => by
    unfold blockAvg blockMean
    rw [(hG x).2]
  simp only [hb]

theorem barField_eq_svec {n : ℕ} (hG : IsLevel G n) {N : ℕ} (Ψ : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (φ : G.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ K)) (i : Fin N) :
    barField G Ψ φ x i = svec G φ x i := by
  have hx := (hG x).1
  have := svec_of_mem G φ ⟨x, hx⟩ i
  simp only at this
  rw [this]
  simp [barField, hx]

theorem restTerm_eq {n : ℕ} (hG : IsLevel G n) (ν : ℝ) {N : ℕ} (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) :
    restTerm G ν D φ = (1 / 2) * ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d, ∑ i,
        ‖svec G φ (x + Pi.single μ 1) i - svec G φ x i‖ ^ 2 +
      ν / 2 * ∑ x, ∑ i, ‖svec G φ x i - D.h x i‖ ^ 2 := by
  unfold restTerm
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => ?_
    simp only [(hG x).1, true_or, ite_true]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [barField_eq_svec hG, barField_eq_svec hG]
  · congr 1
    rw [← hG.sum_Ω (fun x => ∑ i, ‖svec G φ x i - D.h x i‖ ^ 2)]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    rw [svec_of_mem]

theorem svec_restrict {n : ℕ} (hG : IsLevel G n) (hG' : IsLevel G' (n + 1)) (hp : n + 1 ≤ K)
    {N : ℕ} (φ' : G'.Ω 1 × Fin N → ℂ) (y : Torus d (N₀ * L ^ K)) (i : Fin N) :
    svec G ((hG.precedes hG' hp).restrictφ φ') y i = svec G' φ' y i := by
  have hy := (hG y).1
  have hy' := (hG' y).1
  rw [show svec G ((hG.precedes hG' hp).restrictφ φ') y i =
    ((hG.precedes hG' hp).restrictφ φ') (⟨y, hy⟩, i) from svec_of_mem G _ ⟨y, hy⟩ i,
    show svec G' φ' y i = φ' (⟨y, hy'⟩, i) from svec_of_mem G' _ ⟨y, hy'⟩ i]
  rfl

/-- **The key identity** for the action: for the data `D` of level `n` and `D'` of level `n + 1`
with the same `h̃`,
`coupling(θ = D'.Ψ, ψ = D.Ψ) + A_n(D; φ|) = A_{n+1}(D'; φ) + defect`. -/
theorem coupling_add_action {a₁ ν : ℝ} (hL : 2 ≤ L) (ha₁ : 0 < a₁) {n : ℕ}
    (hG : IsLevel G n) (hG' : IsLevel G' (n + 1)) (hp : n + 1 ≤ K) {N : ℕ}
    (D : BgData G N) (D' : BgData G' N) (hh : ∀ x i, D.h x i = D'.h x i)
    (φ' : G'.Ω 1 × Fin N → ℂ) :
    coupling G' a₁ (n + 1) D'.Ψ D.Ψ +
        action G (compWeight L a₁) ν D ((hG.precedes hG' hp).restrictφ φ') =
      action G' (compWeight L a₁) ν D' φ' +
        defect G G' (compWeight L a₁) a₁ n (n + 1) D'.Ψ D.Ψ (svec G' φ') := by
  have hn := hG.bounds
  have key := coupling_add_level (G := G) (G' := G') (a₁ := a₁) hL ha₁ hn.1 hp D'.Ψ D.Ψ
    (svec G' φ')
  rw [action_eq_level_add_rest, action_eq_level_add_rest, levelTerm_eq hG, levelTerm_eq hG',
    restTerm_eq hG, restTerm_eq hG']
  have e : ∀ y i, svec G ((hG.precedes hG' hp).restrictφ φ') y i = svec G' φ' y i :=
    svec_restrict hG hG' hp φ'
  simp only [e, hh]
  linarith [key]

/-- The extension of a field on `Ω₁` to the torus is its restriction when `Ω₁` is everything. -/
theorem svec_eq_apply {n : ℕ} (hG : IsLevel G n) {N : ℕ} (φ : G.Ω 1 × Fin N → ℂ)
    (y : Torus d (N₀ * L ^ K)) (i : Fin N) : svec G φ y i = φ (⟨y, (hG y).1⟩, i) :=
  svec_of_mem G φ ⟨y, (hG y).1⟩ i

/-- The field `φ` on `Ω₁` of level `n` as a field on `Ω'₁` of level `n + 1`
(inverse of `restrictφ`). -/
def liftφ (G' : GeneratingSet d L N₀ K ϱ') {n : ℕ} (hG : IsLevel G n) {N : ℕ}
    (φ : G.Ω 1 × Fin N → ℂ) : G'.Ω 1 × Fin N → ℂ :=
  fun q => φ (⟨q.1.1, (hG q.1.1).1⟩, q.2)

theorem restrictφ_liftφ {n : ℕ} (hG : IsLevel G n) (hG' : IsLevel G' (n + 1)) (hp : n + 1 ≤ K)
    {N : ℕ} (φ : G.Ω 1 × Fin N → ℂ) :
    (hG.precedes hG' hp).restrictφ (liftφ G' hG φ) = φ := by
  funext q
  rfl

theorem isRealUnitField_liftφ {n : ℕ} (hG : IsLevel G n) {N : ℕ}
    {φ : G.Ω 1 × Fin N → ℂ} (hφ : IsRealUnitField G φ) :
    IsRealUnitField G' (liftφ G' hG φ) := fun x => hφ ⟨x.1, (hG x.1).1⟩

theorem isRealUnitField_restrictφ {n : ℕ} (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) {N : ℕ} {φ' : G'.Ω 1 × Fin N → ℂ} (hφ : IsRealUnitField G' φ') :
    IsRealUnitField G ((hG.precedes hG' hp).restrictφ φ') := fun x =>
  hφ ((hG.precedes hG' hp).incl x)

theorem isCompact_realUnit {N : ℕ} :
    IsCompact {φ : G.Ω 1 × Fin N → ℂ | IsRealUnitField G φ} := by
  have hcl : IsClosed {φ : G.Ω 1 × Fin N → ℂ | IsRealUnitField G φ} := by
    have : {φ : G.Ω 1 × Fin N → ℂ | IsRealUnitField G φ} =
        ⋂ x : G.Ω 1, ((⋂ i, {φ : G.Ω 1 × Fin N → ℂ | (φ (x, i)).im = 0}) ∩
          {φ : G.Ω 1 × Fin N → ℂ | ∑ i, ‖φ (x, i)‖ ^ 2 = 1}) := by
      ext φ; simp [IsRealUnitField, Set.mem_iInter]
    rw [this]
    refine isClosed_iInter fun x => (isClosed_iInter fun i => ?_).inter ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · exact isClosed_eq (by fun_prop) (by fun_prop)
  have hb : Bornology.IsBounded {φ : G.Ω 1 × Fin N → ℂ | IsRealUnitField G φ} := by
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun φ hφ => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun q => ?_
    have h1 : ‖φ (q.1, q.2)‖ ^ 2 ≤ ∑ i, ‖φ (q.1, i)‖ ^ 2 :=
      Finset.single_le_sum (f := fun i => ‖φ (q.1, i)‖ ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ q.2)
    rw [(hφ q.1).2] at h1
    show ‖φ (q.1, q.2)‖ ≤ 1
    nlinarith [norm_nonneg (φ (q.1, q.2))]
  exact Metric.isCompact_of_isClosed_isBounded hcl hb

theorem continuous_action {n : ℕ} (hG : IsLevel G n) (a : ℕ → ℝ) (ν : ℝ) {N : ℕ}
    (D : BgData G N) : Continuous fun φ : G.Ω 1 × Fin N → ℂ => action G a ν D φ := by
  have hs : ∀ (y : Torus d (N₀ * L ^ K)) (i : Fin N),
      Continuous fun φ : G.Ω 1 × Fin N → ℂ => svec G φ y i := fun y i => by
    simp only [svec_eq_apply hG]
    fun_prop
  have e : (fun φ : G.Ω 1 × Fin N → ℂ => action G a ν D φ) = fun φ =>
      (1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) * ∑ x, ∑ i,
        ‖D.Ψ x i - blockMean G n (fun y => svec G φ y i) x‖ ^ 2 +
      ((1 / 2) * ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d, ∑ i,
        ‖svec G φ (x + Pi.single μ 1) i - svec G φ x i‖ ^ 2 +
      ν / 2 * ∑ x, ∑ i, ‖svec G φ x i - D.h x i‖ ^ 2) := by
    funext φ
    rw [action_eq_level_add_rest, levelTerm_eq hG, restTerm_eq hG]
  rw [e]
  unfold blockMean
  fun_prop

/-- The whole-lattice generating set `levelGS j` of the class has level `j`. -/
theorem isLevel_levelGS {N₁ m₁ k : ℕ} [NeZero N₁] {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    IsLevel (Balaban.SmallField.Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk) j := by
  classical
  intro x
  have hx : x ∈ (Balaban.SmallField.Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk).layer j := by
    simp [GeneratingSet.layer, Balaban.SmallField.Def6.levelGS]
  refine ⟨?_, GeneratingSet.layerIndex_eq _ hj1 hjk hx⟩
  simp [Balaban.SmallField.Def6.levelGS, hj1]

end Level

section CriticalPoint

variable {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'} {a₁ ν : ℝ} {n : ℕ}

/-- **The function `J_k(θ, ·)` of Lemma 2.2 (b)**, with the background field `bgField`:
`J_k(θ, ψ) = ½ a₁ L^{-2(n+1)} ‖θ - Q ψ‖² + A_n(ψ, φ_n(ψ))`, in the fine units of Background
(`n = k`; the `η`-unit value is `L^{-k(d-2)}` times this one, FLUCTUATION §1.1).  The datum of `ψ`
is the `BgData` `D` (the lifted field `D.Ψ` and `h̃ = D.h`). -/
noncomputable def Jbg (G : GeneratingSet d L N₀ K ϱ) (G' : GeneratingSet d L N₀ K ϱ')
    (a : ℕ → ℝ) (a₁ ν : ℝ) (n : ℕ) {N : ℕ} (θ : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (D : BgData G N) : ℝ :=
  coupling G' a₁ (n + 1) θ D.Ψ + action G a ν D (bgField G a ν D)

/-- **`J_k(θ, ψ)` as the minimum over the sphere**: `J_k(θ, ψ) = min_{|φ| = 1} [coupling + A_n(ψ, φ)]`,
defined for every real datum (the global form used in Lemma 2.2 (b)). -/
noncomputable def Jinf (G : GeneratingSet d L N₀ K ϱ) (G' : GeneratingSet d L N₀ K ϱ')
    (a : ℕ → ℝ) (a₁ ν : ℝ) (n : ℕ) {N : ℕ} (θ : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (D : BgData G N) : ℝ :=
  ⨅ φ : {φ : G.Ω 1 × Fin N → ℂ // IsRealUnitField G φ},
    coupling G' a₁ (n + 1) θ D.Ψ + action G a ν D φ.1

section Setup

/-- The lower bound: for every datum `D` of level `n` with the same `h̃` and every real unit field,
the total is at least the minimal action of level `n + 1`. -/
theorem total_ge (hL : 2 ≤ L) (ha₁ : 0 < a₁) (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (D : BgData G N) (D' : BgData G' N) (hh : ∀ x i, D.h x i = D'.h x i)
    {φ' : G'.Ω 1 × Fin N → ℂ}
    (hmin : ∀ σ : G'.Ω 1 × Fin N → ℂ, IsRealUnitField G' σ →
      action G' (compWeight L a₁) ν D' φ' ≤ action G' (compWeight L a₁) ν D' σ)
    {φ : G.Ω 1 × Fin N → ℂ} (hφ : IsRealUnitField G φ) :
    action G' (compWeight L a₁) ν D' φ' ≤
      coupling G' a₁ (n + 1) D'.Ψ D.Ψ + action G (compWeight L a₁) ν D φ := by
  have key := coupling_add_action (ν := ν) hL ha₁ hG hG' hp D D' hh (liftφ G' hG φ)
  rw [restrictφ_liftφ hG hG' hp] at key
  have h1 := defect_nonneg (G := G) (G' := G') (a₁ := a₁) hL ha₁ hG.bounds.1 D'.Ψ D.Ψ
    (svec G' (liftφ G' hG φ))
  have h2 := hmin _ (isRealUnitField_liftφ hG hφ)
  linarith

theorem data_blockConst (hG' : IsLevel G' (n + 1)) (D' : BgData G' N) (x y : Torus d (N₀ * L ^ K))
    (i : Fin N) (hy : y ∈ G'.blk (n + 1) x) : D'.Ψ y i = D'.Ψ x i := by
  have hb := hG'.bounds
  exact congrFun (D'.Ψ_layerConst (n + 1) hb.1 hb.2 x (hG'.mem_layer x) y hy) i

theorem Jinf_eq_of_isMinOn {D : BgData G N} (θ : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    {a : ℕ → ℝ} {φ0 : G.Ω 1 × Fin N → ℂ} (hφ0 : IsRealUnitField G φ0)
    (hmin : ∀ φ : G.Ω 1 × Fin N → ℂ, IsRealUnitField G φ →
      coupling G' a₁ (n + 1) θ D.Ψ + action G a ν D φ0 ≤
        coupling G' a₁ (n + 1) θ D.Ψ + action G a ν D φ)
    (hbdd : ∃ B : ℝ, ∀ φ : G.Ω 1 × Fin N → ℂ, IsRealUnitField G φ →
      B ≤ coupling G' a₁ (n + 1) θ D.Ψ + action G a ν D φ) :
    Jinf G G' a a₁ ν n θ D = coupling G' a₁ (n + 1) θ D.Ψ + action G a ν D φ0 := by
  obtain ⟨B, hB⟩ := hbdd
  have hb : BddBelow (Set.range fun φ : {φ : G.Ω 1 × Fin N → ℂ // IsRealUnitField G φ} =>
      coupling G' a₁ (n + 1) θ D.Ψ + action G a ν D φ.1) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨φ, rfl⟩
    exact hB φ.1 φ.2
  apply le_antisymm
  · exact ciInf_le hb (⟨φ0, hφ0⟩ : {φ : G.Ω 1 × Fin N → ℂ // IsRealUnitField G φ})
  · have : Nonempty {φ : G.Ω 1 × Fin N → ℂ // IsRealUnitField G φ} := ⟨⟨φ0, hφ0⟩⟩
    exact le_ciInf fun φ => hmin φ.1 φ.2

/-- **Uniqueness of the global minimiser** (Lemma 2.2 (b)): if `D` has the same `h̃` as `D'` and
`D.Ψ ≠ Ψ(θ, φ')` somewhere, then `J_k(θ, D) = min_φ [...]` is strictly larger than the minimal
action of level `n + 1`. -/
theorem lt_Jinf_of_ne (hL : 2 ≤ L) (ha₁ : 0 < a₁) (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (D : BgData G N) (D' : BgData G' N) (hh : ∀ x i, D.h x i = D'.h x i)
    {φ' : G'.Ω 1 × Fin N → ℂ} (hunit : IsRealUnitField G' φ')
    (hmin : ∀ σ : G'.Ω 1 × Fin N → ℂ, IsRealUnitField G' σ →
      action G' (compWeight L a₁) ν D' φ' ≤ action G' (compWeight L a₁) ν D' σ)
    (huniq : ∀ σ : G'.Ω 1 × Fin N → ℂ, IsRealUnitField G' σ →
      action G' (compWeight L a₁) ν D' σ ≤ action G' (compWeight L a₁) ν D' φ' → σ = φ')
    (hne : ∃ x i, D.Ψ x i ≠ psiStar G G' (compWeight L a₁) n (n + 1) D'.Ψ (svec G' φ') x i) :
    action G' (compWeight L a₁) ν D' φ' <
      Jinf G G' (compWeight L a₁) a₁ ν n D'.Ψ D := by
  have hbdd : ∃ B : ℝ, ∀ φ : G.Ω 1 × Fin N → ℂ, IsRealUnitField G φ →
      B ≤ coupling G' a₁ (n + 1) D'.Ψ D.Ψ + action G (compWeight L a₁) ν D φ :=
    ⟨_, fun φ hφ => total_ge hL ha₁ hG hG' hp D D' hh hmin hφ⟩
  have hne0 : {φ : G.Ω 1 × Fin N → ℂ | IsRealUnitField G φ}.Nonempty :=
    ⟨_, isRealUnitField_restrictφ hG hG' hp hunit⟩
  have hcont : Continuous fun φ : G.Ω 1 × Fin N → ℂ =>
      coupling G' a₁ (n + 1) D'.Ψ D.Ψ + action G (compWeight L a₁) ν D φ :=
    continuous_const.add (continuous_action hG _ _ D)
  obtain ⟨φ0, hφ0, hmin0⟩ := (isCompact_realUnit (G := G) (N := N)).exists_isMinOn hne0
    hcont.continuousOn
  rw [Jinf_eq_of_isMinOn D'.Ψ hφ0 (fun φ hφ => hmin0 hφ) hbdd]
  by_contra hcon
  push Not at hcon
  have hge := total_ge hL ha₁ hG hG' hp D D' hh hmin hφ0
  have key := coupling_add_action (ν := ν) hL ha₁ hG hG' hp D D' hh (liftφ G' hG φ0)
  rw [restrictφ_liftφ hG hG' hp] at key
  have hdef := defect_nonneg (G := G) (G' := G') (a₁ := a₁) hL ha₁ hG.bounds.1 D'.Ψ D.Ψ
    (svec G' (liftφ G' hG φ0))
  have hunit0 := isRealUnitField_liftφ (G' := G') hG hφ0
  have hm0 := hmin _ hunit0
  have hEq : liftφ G' hG φ0 = φ' := huniq _ hunit0 (by linarith)
  have hdef0 : defect G G' (compWeight L a₁) a₁ n (n + 1) D'.Ψ D.Ψ (svec G' φ') = 0 := by
    rw [← hEq]; linarith
  rw [defect_eq_zero_iff hL ha₁ hG.bounds.1 hp
    D'.Ψ D.Ψ (svec G' φ') (fun x y i hy => data_blockConst hG' D' x y i hy)] at hdef0
  obtain ⟨x, i, hxi⟩ := hne
  exact hxi (hdef0 x i)

/-- For a datum in the real domain, `J_k` computed with `bgField` is the minimum over the sphere. -/
theorem Jbg_eq_Jinf (H : BgHyp d L K ϱ (compWeight L a₁) ν) (D : BgData G N)
    (hD : InUnionDomainR G (bgC1 d L N) ν D) (θ : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    Jbg G G' (compWeight L a₁) a₁ ν n θ D = Jinf G G' (compWeight L a₁) a₁ ν n θ D := by
  obtain ⟨⟨φ0, hmin0, hu0⟩, hunit, -⟩ := theorem71 H hD
  have hf : bgField G (compWeight L a₁) ν D = φ0 := bgField_eq hmin0 hu0
  rw [hf] at hunit
  symm
  unfold Jbg
  rw [hf]
  have hle : ∀ φ : G.Ω 1 × Fin N → ℂ, IsRealUnitField G φ →
      coupling G' a₁ (n + 1) θ D.Ψ + action G (compWeight L a₁) ν D φ0 ≤
        coupling G' a₁ (n + 1) θ D.Ψ + action G (compWeight L a₁) ν D φ := fun φ hφ => by
    have := hmin0.2.2 φ hφ
    linarith
  exact Jinf_eq_of_isMinOn θ hunit hle ⟨_, fun φ hφ => hle φ hφ⟩

theorem composeData_Ψ_eq_psiStar (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ) (D' : BgData G' N)
    (x : Torus d (N₀ * L ^ K)) (i : Fin N) :
    (composeData (hG.precedes hG' hp) a φ' D').Ψ x i =
      psiStar G G' a n (n + 1) D'.Ψ (svec G' φ') x i := by
  show composeField G G' a φ' D'.Ψ x i = _
  rw [composeField_of_mem a φ' D'.Ψ (hG x).1 i, (hG x).2, (hG' x).2]
  rfl

theorem composeData_h (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ) (D' : BgData G' N)
    (x : Torus d (N₀ * L ^ K)) (i : Fin N) :
    (composeData (hG.precedes hG' hp) a φ' D').h x i = D'.h x i := by
  simp [composeData, (hG x).1]

/-- **Lemma 2.2 (b), (2.1) and (2.2): the critical point, real data** (FLUCTUATION §2.2; BG
Theorem 5.2 (4), Theorem 6.1 (ii), (iv) as landed in `theorem73_real`).  Let `G` (level `n = k`)
and `G'` (level `n + 1`) be whole-lattice generating sets on the common fine torus, `a = compWeight L a₁`
the weights, and `D'` real data of level `n + 1` (the pair `(θ, h)`) in the domain of the
background field (`thm73C1`).  Put `φ' = φ_{k+1}(θ) = bgField G' D'` and `ψ^{(k)} := composeData …`
(the point `Ψ(θ, φ_{k+1}(θ))` of (2.1)).  Then:

* `ψ^{(k)}` is real data of level `n` in the real domain, and equals `psiStar` of `(θ, φ')`;
* `J_k(θ, ψ^{(k)}) = A_{k+1}(θ, φ_{k+1}(θ))`, both with `Jbg` (the background field) and with
  `Jinf` (the minimum over the sphere);
* every other datum `D` with the same `h̃` has `Jinf(D) > Jinf(ψ^{(k)})`: `ψ^{(k)}` is the unique
  global minimiser of `ψ ↦ J_k(θ, ψ)`;
* (2.2): `φ_k(ψ^{(k)}) = φ_{k+1}(θ)` and `α_k(ψ^{(k)}) = α_{k+1}(θ)` (restrictions to `Ω₁ ⊆ Ω'₁`). -/
theorem criticalPoint_real (ha₁ : 0 < a₁) (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (H : BgHyp d L K ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L K ϱ' (compWeight L a₁) ν) (D' : BgData G' N)
    (hD' : InUnionDomainR G' (thm73C1 d L N) ν D') :
    (composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgField G' (compWeight L a₁) ν D') D').IsReal ∧
    InUnionDomainR G (bgC1 d L N) ν (composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgField G' (compWeight L a₁) ν D') D') ∧
    (∀ x i, (composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgField G' (compWeight L a₁) ν D') D').Ψ x i =
      psiStar G G' (compWeight L a₁) n (n + 1) D'.Ψ
        (svec G' (bgField G' (compWeight L a₁) ν D')) x i) ∧
    Jbg G G' (compWeight L a₁) a₁ ν n D'.Ψ (composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgField G' (compWeight L a₁) ν D') D') =
      action G' (compWeight L a₁) ν D' (bgField G' (compWeight L a₁) ν D') ∧
    Jinf G G' (compWeight L a₁) a₁ ν n D'.Ψ (composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgField G' (compWeight L a₁) ν D') D') =
      action G' (compWeight L a₁) ν D' (bgField G' (compWeight L a₁) ν D') ∧
    (∀ D : BgData G N, (∀ x i, D.h x i = D'.h x i) →
      (∃ x i, D.Ψ x i ≠ (composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgField G' (compWeight L a₁) ν D') D').Ψ x i) →
      Jinf G G' (compWeight L a₁) a₁ ν n D'.Ψ (composeData (hG.precedes hG' hp)
        (compWeight L a₁) (bgField G' (compWeight L a₁) ν D') D') <
        Jinf G G' (compWeight L a₁) a₁ ν n D'.Ψ D) ∧
    bgField G (compWeight L a₁) ν (composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgField G' (compWeight L a₁) ν D') D') =
      (hG.precedes hG' hp).restrictφ (bgField G' (compWeight L a₁) ν D') ∧
    bgMult G (compWeight L a₁) ν (composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgField G' (compWeight L a₁) ν D') D') =
      (hG.precedes hG' hp).restrictα (bgMult G' (compWeight L a₁) ν D') := by
  have hL3 : 2 ≤ L := by have := H.hL; omega
  have hd0 : 0 < d := by have := H.hd; omega
  have hDU : InUnionDomainR G' (bgC1 d L N) ν D' := by
    obtain ⟨δ, hδ0, hδc, hD⟩ := hD'
    exact ⟨δ, hδ0, (thm73_small (L := L) (N := N) hd0 hδ0 hδc).1, hD⟩
  obtain ⟨⟨φ0, hmin0, hu0⟩, hunit', -⟩ := theorem71 H' hDU
  have hf' : bgField G' (compWeight L a₁) ν D' = φ0 := bgField_eq hmin0 hu0
  rw [hf'] at hunit' ⊢
  have hmin : ∀ σ : G'.Ω 1 × Fin N → ℂ, IsRealUnitField G' σ →
      action G' (compWeight L a₁) ν D' φ0 ≤ action G' (compWeight L a₁) ν D' σ :=
    fun σ hσ => hmin0.2.2 σ hσ
  have huniq : ∀ σ : G'.Ω 1 × Fin N → ℂ, IsRealUnitField G' σ →
      action G' (compWeight L a₁) ν D' σ ≤ action G' (compWeight L a₁) ν D' φ0 → σ = φ0 :=
    fun σ hσ hle => hu0 σ ⟨hmin0.1, hσ, fun τ hτ => hle.trans (hmin τ hτ)⟩
  obtain ⟨hdom, hreal, hfield, hmult⟩ := theorem73_real ha₁ H H' (hG.precedes hG' hp) hD'
  rw [hf'] at hdom hreal hfield hmult
  set ψ := composeData (hG.precedes hG' hp) (compWeight L a₁) φ0 D' with hψ
  have hΨ : ∀ x i, ψ.Ψ x i = psiStar G G' (compWeight L a₁) n (n + 1) D'.Ψ (svec G' φ0) x i :=
    composeData_Ψ_eq_psiStar hG hG' hp _ φ0 D'
  have hh : ∀ x i, ψ.h x i = D'.h x i := composeData_h hG hG' hp _ φ0 D'
  have hdef0 : defect G G' (compWeight L a₁) a₁ n (n + 1) D'.Ψ ψ.Ψ (svec G' φ0) = 0 :=
    (defect_eq_zero_iff hL3 ha₁ hG.bounds.1 hp D'.Ψ ψ.Ψ (svec G' φ0)
      (fun x y i hy => data_blockConst hG' D' x y i hy)).2 hΨ
  have hcore := coupling_add_action (ν := ν) hL3 ha₁ hG hG' hp ψ D' hh φ0
  rw [hdef0, add_zero] at hcore
  have hlower : ∀ φ : G.Ω 1 × Fin N → ℂ, IsRealUnitField G φ →
      coupling G' a₁ (n + 1) D'.Ψ ψ.Ψ + action G (compWeight L a₁) ν ψ
        ((hG.precedes hG' hp).restrictφ φ0) ≤
      coupling G' a₁ (n + 1) D'.Ψ ψ.Ψ + action G (compWeight L a₁) ν ψ φ := fun φ hφ => by
    have := total_ge hL3 ha₁ hG hG' hp ψ D' hh hmin hφ
    linarith
  have hJinf : Jinf G G' (compWeight L a₁) a₁ ν n D'.Ψ ψ =
      action G' (compWeight L a₁) ν D' φ0 := by
    rw [Jinf_eq_of_isMinOn D'.Ψ (isRealUnitField_restrictφ hG hG' hp hunit') hlower
      ⟨_, hlower⟩]
    exact hcore
  refine ⟨hreal, hdom, hΨ, ?_, hJinf, ?_, hfield, hmult⟩
  · unfold Jbg
    rw [hfield]
    exact hcore
  · intro D hhD hne
    rw [hJinf]
    refine lt_Jinf_of_ne hL3 ha₁ hG hG' hp D D' hhD hunit' hmin huniq ?_
    obtain ⟨x, i, hxi⟩ := hne
    exact ⟨x, i, by rw [← hΨ]; exact hxi⟩

/-- **Lemma 2.2 (c): the critical point, complex data** (BG Theorem 6.1 (ii), (iv), landed as
`theorem73_complex`, with the complex small solution `bgFieldC`).  For complex data `D'` of level
`n + 1` in `𝒟(𝔹'_k)` (`δ ≤ thm73C1`), `ψ^{(k)} := composeData … (bgFieldC D') D'` is the point
`Ψ(θ, φ_{k+1}(θ))` of (2.1) with the complex small solution, lies in the complex domain of level
`n`, and satisfies (2.2): its small solution is the restriction of `(φ_{k+1}, α_{k+1})`. -/
theorem criticalPoint_complex (ha₁ : 0 < a₁) (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (H : BgHyp d L K ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L K ϱ' (compWeight L a₁) ν) (D' : BgData G' N)
    (hD' : InUnionDomainC G' (bgC0 d L N) (thm73C1 d L N) ν D') :
    InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν (composeData (hG.precedes hG' hp)
        (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D') ∧
    (∀ x i, (composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D').Ψ x i =
      psiStar G G' (compWeight L a₁) n (n + 1) D'.Ψ
        (svec G' (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')) x i) ∧
    bgFieldC G (compWeight L a₁) ν (bgC0 d L N) (composeData (hG.precedes hG' hp)
        (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D') =
      (hG.precedes hG' hp).restrictφ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') ∧
    bgMultC G (compWeight L a₁) ν (bgC0 d L N) (composeData (hG.precedes hG' hp)
        (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D') =
      (hG.precedes hG' hp).restrictα (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D') ∧
    IsSmallSolution G (compWeight L a₁) ν (bgC0 d L N) (composeData (hG.precedes hG' hp)
        (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D')
      ((hG.precedes hG' hp).restrictφ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D'))
      ((hG.precedes hG' hp).restrictα (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')) := by
  obtain ⟨hdom, hfield, hmult⟩ := theorem73_complex ha₁ H H' (hG.precedes hG' hp) hD'
  refine ⟨hdom, composeData_Ψ_eq_psiStar hG hG' hp _ _ D', hfield, hmult, ?_⟩
  have := (theorem72 H hdom).2.1
  rwa [hfield, hmult] at this

/-- The mass term of the action: `A_ν = A_0 + (ν/2) ∑ |φ - h̃|²`, i.e.
`J_k = J⁰_k + (ν_k/2) ‖φ_k - h‖²` of Lemma 2.2 (d) (with `φ_k` the `ν`-free background). -/
theorem action_mass_split (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    action G a ν D φ = action G a 0 D φ + ν / 2 * ∑ x : G.Ω 1, ∑ i, ‖φ (x, i) - D.h x i‖ ^ 2 := by
  unfold action
  ring

/-- **Lemma 2.2 (d): the `ν`-free convention.**  The statements (a)--(c) do not use the mass: the
theorems above hold for every `ν ≥ 0`, in particular for `ν = 0`, the `ν`-free backgrounds and the
function `J⁰_k` (the action without the mass term).  This is `criticalPoint_real` at `ν = 0`. -/
theorem criticalPoint_real_nuFree (ha₁ : 0 < a₁) (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (H : BgHyp d L K ϱ (compWeight L a₁) 0)
    (H' : BgHyp d L K ϱ' (compWeight L a₁) 0) (D' : BgData G' N)
    (hD' : InUnionDomainR G' (thm73C1 d L N) 0 D') :
    (composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgField G' (compWeight L a₁) 0 D') D').IsReal ∧
    InUnionDomainR G (bgC1 d L N) 0 (composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgField G' (compWeight L a₁) 0 D') D') ∧
    (∀ x i, (composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgField G' (compWeight L a₁) 0 D') D').Ψ x i =
      psiStar G G' (compWeight L a₁) n (n + 1) D'.Ψ
        (svec G' (bgField G' (compWeight L a₁) 0 D')) x i) ∧
    Jbg G G' (compWeight L a₁) a₁ 0 n D'.Ψ (composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgField G' (compWeight L a₁) 0 D') D') =
      action G' (compWeight L a₁) 0 D' (bgField G' (compWeight L a₁) 0 D') ∧
    Jinf G G' (compWeight L a₁) a₁ 0 n D'.Ψ (composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgField G' (compWeight L a₁) 0 D') D') =
      action G' (compWeight L a₁) 0 D' (bgField G' (compWeight L a₁) 0 D') ∧
    (∀ D : BgData G N, (∀ x i, D.h x i = D'.h x i) →
      (∃ x i, D.Ψ x i ≠ (composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgField G' (compWeight L a₁) 0 D') D').Ψ x i) →
      Jinf G G' (compWeight L a₁) a₁ 0 n D'.Ψ (composeData (hG.precedes hG' hp)
        (compWeight L a₁) (bgField G' (compWeight L a₁) 0 D') D') <
        Jinf G G' (compWeight L a₁) a₁ 0 n D'.Ψ D) ∧
    bgField G (compWeight L a₁) 0 (composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgField G' (compWeight L a₁) 0 D') D') =
      (hG.precedes hG' hp).restrictφ (bgField G' (compWeight L a₁) 0 D') ∧
    bgMult G (compWeight L a₁) 0 (composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgField G' (compWeight L a₁) 0 D') D') =
      (hG.precedes hG' hp).restrictα (bgMult G' (compWeight L a₁) 0 D') :=
  criticalPoint_real (ν := 0) ha₁ hG hG' hp H H' D' hD'

end Setup

end CriticalPoint

end Balaban.Fluctuation
