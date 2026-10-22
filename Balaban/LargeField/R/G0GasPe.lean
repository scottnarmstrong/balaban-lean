/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.G0Engine
public import Balaban.LargeField.R.G0GasGeom
public import Balaban.LargeField.R.G0Config

/-!
# G0: the convergence of the expansion of the gas of a kept configuration

`decOp_pe_hole` on the actual gas of `G0Gas` (P7 (3.26)–(3.28); LFR Lemma III.10.5):

* `HopConsts`, `GasHop`: **the analytic clauses of (H-op)** for the gas of a kept configuration at
  the external variables `e` (W2's export, one named structure): the reference measures are
  probability measures, the weights depend on the internal configuration through their charged
  supports and are measurable, the heavy weights are integrable, the sup bound of the active
  couplings, the weighted counts of the heavy weights, the entropy of the active couplings, and
  the PE inequalities, at the graph degree `2d`, the subadditivity constant `c = 0` and `c₂ = 1`;
* `gasP_pe`: under `GasHop`, when the hole lies in the kept region (`hS₀`) and the cluster
  supports miss it (`hsupp`, point (2) of the G0 review): the expected decorated partition function
  is `exp Σ_X gasP X e`, with the weighted bound `Σ_{X ∋ q} |gasP X e| e^{κ_p steiner(X ∖ S₀)} ≤ α`
  at every cube `q` outside the hole and `|Σ_X gasP X e| ≤ |𝕋_k ∖ S₀| α`.

The geometric hypotheses of the engine are proved (`G0GasGeom`, `G0TorusGeom`): connected and
hole-closed full supports, charged contact of a domain with the clusters it meets, nonempty heavy
charged supports, the subadditivity of the Steiner size over contact-connected families
(`steiner_unionCs_le`), the degree bound of the cube graph (`latGraph_degree_le`).
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset MeasureTheory Balaban Balaban.Polymer Balaban.LargeField.Def7

namespace Balaban.LargeField.G0

/-- The constants of (H-op) for the gas of a kept configuration (LFR Lemma III.10.5). -/
structure HopConsts where
  /-- the sup bound of the couplings -/
  B0 : ℝ
  /-- the decay rate of the couplings -/
  κc : ℝ
  /-- the activity rate (`κ_g`) -/
  κg : ℝ
  /-- the rate of the local terms (`κ_p`) -/
  κp : ℝ
  /-- the KP parameter -/
  α : ℝ
  /-- the prefactor rate of the heavy weights -/
  p : ℝ
  /-- the size rate of the heavy weights -/
  h : ℝ
  /-- the entropy constant of the couplings -/
  K0g : ℝ
  /-- the entropy constant of the heavy objects -/
  K0h : ℝ

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N k : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
  {rep : Rep S n R k0 K M N geo cs P k} {m₁ : ℕ} {ϱ : ℝ}

/-- **The analytic clauses of (H-op) for the gas of a kept configuration** at the external
variables `e` (LFR Lemma III.10.5 and (H-op); W2's export): the hypotheses of `decOp_pe_hole` that
are not geometric, for the heavy objects `holeCl S₀ (clSupp 𝒞)`, the light objects the connected
domains decorated by the clusters they meet, the weights `gasTau`, `e^{gasCoupling} - 1`, and the
reference measures `pres.μ`, with the degree `2d`, `c = 0`, `c₂ = 1`. -/
structure GasHop (Kc : HistConfig S n R k0 K M k) (C : SFCtx S n R M K N k m₁ ϱ)
    (hv : EuclideanSpace ℝ (Fin N)) (vc : Def7v2.CorrCoef S.d) (pres : RemPres rep)
    (Y : Set (Torus S.d (n k))) (S₀ : Finset (Torus S.d (n k)))
    (keptT : Finset (Torus S.d (n k)) → BExt S n M K N → ℂ) (e : BExt S n M K N)
    (hc : HopConsts) : Prop where
  prob : ∀ b, IsProbabilityMeasure (pres.μ b)
  hB0 : 0 ≤ hc.B0
  hκg : 0 ≤ hc.κg
  hκc : hc.κg ≤ hc.κc
  hp : 0 ≤ hc.p
  hκp : 0 ≤ hc.κp
  hK0g : 0 ≤ hc.K0g
  hK1 : 1 ≤ hc.K0h
  hβd : ∀ y, DepOn
    (decCy S₀ (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl)) (fun X : LDom S n k => holeCl S₀ X.1)
      (fun X Cl => gasNear rep Kc X.1 Cl) y)
    (decβ (fun (X : LDom S n k) (Cl : RemCl rep Kc) => gasNear rep Kc X.1 Cl)
      (fun X Sc Φ => gasCoupling Kc C hv vc pres Y keptT X.1 Sc e Φ) y)
  hτd : ∀ Cl, DepOn (decZs S₀ (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl)) Cl)
    (fun Φ => gasTau Kc pres Cl e Φ)
  hβm : ∀ y, Measurable
    (decβ (fun (X : LDom S n k) (Cl : RemCl rep Kc) => gasNear rep Kc X.1 Cl)
      (fun X Sc Φ => gasCoupling Kc C hv vc pres Y keptT X.1 Sc e Φ) y)
  hτm : ∀ Cl, Measurable (fun Φ => gasTau Kc pres Cl e Φ)
  hτi : ∀ Cl, Integrable (fun Φ => gasTau Kc pres Cl e Φ) (Measure.pi pres.μ)
  hB : ∀ Γ : Finset (RemCl rep Kc),
    (∀ m ∈ Γ, ∀ m' ∈ Γ, m ≠ m' →
      Disjoint (decZs S₀ (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl)) m)
        (decZs S₀ (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl)) m')) →
    ∀ y, decAct (fun (X : LDom S n k) (Cl : RemCl rep Kc) => gasNear rep Kc X.1 Cl) y Γ →
    ∀ Φ, (∀ m ∈ Γ, gasTau Kc pres m e Φ ≠ 0) →
      ‖decβ (fun (X : LDom S n k) (Cl : RemCl rep Kc) => gasNear rep Kc X.1 Cl)
          (fun X Sc Φ => gasCoupling Kc C hv vc pres Y keptT X.1 Sc e Φ) y Φ‖ ≤
        hc.B0 * Real.exp (-hc.κc * (steiner (Localization.latGraph S.d (n k))
          (decCy S₀ (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl))
            (fun X : LDom S n k => holeCl S₀ X.1) (fun X Cl => gasNear rep Kc X.1 Cl) y) : ℝ))
  hent : DecEnt (Localization.latGraph S.d (n k)) S₀
    (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl)) (fun X : LDom S n k => holeCl S₀ X.1)
    (fun X Cl => gasNear rep Kc X.1 Cl) hc.κc hc.κg hc.K0g
  hcount : DecCount S₀ (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl))
    (fun Cl Φ => gasTau Kc pres Cl e Φ) pres.μ hc.K0h hc.p hc.h
  hh : hc.B0 * Real.exp hc.B0 * Real.exp (hc.κg * 0) * hc.K0g + hc.κg * (1 + 0) + 1 + 3 +
    Real.log hc.K0h ≤ hc.h
  hq : ((2 * S.d : ℕ) : ℝ) ^ 2 * 2 ^ (2 * S.d + 1) *
    Real.exp (-((hc.κg - 2) - hc.κp - hc.α)) < 1
  hcond : 3 * Real.exp (-hc.p) * 2 ^ (2 * S.d + 1) * Real.exp (-((hc.κg - 2) - hc.κp - hc.α)) /
      (1 - ((2 * S.d : ℕ) : ℝ) ^ 2 * 2 ^ (2 * S.d + 1) *
        Real.exp (-((hc.κg - 2) - hc.κp - hc.α))) ≤ hc.α

/-- With the cluster supports missing the hole, the charged support of a heavy object is the
cluster support. -/
theorem decZs_eq_clSupp {Kc : HistConfig S n R k0 K M k} {S₀ : Finset (Torus S.d (n k))}
    (Cl : RemCl rep Kc) (hsupp : Disjoint (clSupp Cl) S₀) :
    decZs S₀ (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl)) Cl = clSupp Cl := by
  ext b
  simp only [decZs, Finset.mem_sdiff]
  constructor
  · rintro ⟨hb, hbS⟩
    rcases Finset.mem_union.mp hb with h | h
    · exact h
    · obtain ⟨a, -, -, hbc⟩ := (Finset.mem_filter.mp h).2
      exact absurd (nnComp_subset _ hbc) hbS
  · intro hb
    exact ⟨subset_holeCl S₀ _ hb, Finset.disjoint_left.mp hsupp hb⟩

/-- **The expansion of the gas of a kept configuration converges** (P7 (3.26)–(3.28); LFR Lemma
III.10.5): under the analytic clauses of (H-op) (`GasHop`), with the hole inside the kept region
and the cluster supports missing it, the expected decorated partition function is
`exp Σ_X gasP X e`, the local terms obey the weighted bound at the cubes outside the hole, and
`|Σ_X gasP X e| ≤ |𝕋_k ∖ S₀| α`. -/
theorem gasP_pe {Kc : HistConfig S n R k0 K M k} (C : SFCtx S n R M K N k m₁ ϱ)
    (hv : EuclideanSpace ℝ (Fin N)) (vc : Def7v2.CorrCoef S.d) (pres : RemPres rep)
    (Y : Set (Torus S.d (n k))) {S₀ : Finset (Torus S.d (n k))}
    (keptT : Finset (Torus S.d (n k)) → BExt S n M K N → ℂ) (e : BExt S n M K N)
    {hc : HopConsts} (hop : GasHop Kc C hv vc pres Y S₀ keptT e hc)
    (hS₀ : ∀ b ∈ S₀, ∃ m ∈ Kc.members, b ∈ m.1)
    (hsupp : ∀ Cl : RemCl rep Kc, Disjoint (clSupp Cl) S₀) :
    decXi S₀ (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl))
        (fun (X : LDom S n k) Cl => gasNear rep Kc X.1 Cl)
        (fun Cl Φ => gasTau Kc pres Cl e Φ)
        (fun X Sc Φ => gasCoupling Kc C hv vc pres Y keptT X.1 Sc e Φ) pres.μ =
      Complex.exp (∑ X : Finset (Torus S.d (n k)), gasP Kc C hv vc pres Y S₀ keptT X e) ∧
    (∀ q ∉ S₀, kpSum (Localization.latGraph S.d (n k)) S₀ hc.κp
      (fun X => gasP Kc C hv vc pres Y S₀ keptT X e) q ≤ hc.α) ∧
    ‖∑ X : Finset (Torus S.d (n k)), gasP Kc C hv vc pres Y S₀ keptT X e‖ ≤
      (chargedCard S₀ : ℝ) * hc.α := by
  have := hop.prob
  have hzd : ∀ m : RemCl rep Kc, (steiner (Localization.latGraph S.d (n k))
      (decZs S₀ (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl)) m) : ℝ) ≤
      1 * (decZs S₀ (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl)) m).card := by
    intro m
    rw [decZs_eq_clSupp m (hsupp m), one_mul]
    exact_mod_cast steiner_le (isAnimal_clSupp m) subset_rfl
  have hG3 : ∀ Cf : Finset (DecObj (fun (X : LDom S n k) (Cl : RemCl rep Kc) =>
        gasNear rep Kc X.1 Cl) ⊕ RemCl rep Kc),
      ConnSet (gasCs (decCy S₀ (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl))
        (fun X : LDom S n k => holeCl S₀ X.1) (fun X Cl => gasNear rep Kc X.1 Cl))
        (decZs S₀ (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl)))) Cf →
      actGasA (decAct (fun (X : LDom S n k) (Cl : RemCl rep Kc) => gasNear rep Kc X.1 Cl))
        (decZs S₀ (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl))) Cf →
      (steiner (Localization.latGraph S.d (n k)) (unionCs (gasCs (decCy S₀
        (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl)) (fun X : LDom S n k => holeCl S₀ X.1)
        (fun X Cl => gasNear rep Kc X.1 Cl))
        (decZs S₀ (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl)))) Cf) : ℝ) ≤
        ∑ t ∈ Cf, (steiner (Localization.latGraph S.d (n k)) (gasCs (decCy S₀
          (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl)) (fun X : LDom S n k => holeCl S₀ X.1)
          (fun X Cl => gasNear rep Kc X.1 Cl))
          (decZs S₀ (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl))) t) : ℝ) +
          0 * ((Cf.card : ℝ) - 1) := by
    intro Cf hconn _
    rw [zero_mul, add_zero]
    refine steiner_unionCs_le _ hconn fun t _ => ?_
    rcases t with y | m
    · refine ⟨_, gas_hSx (S₀ := S₀) y, fun b hb => ?_⟩
      simp only [gasCs, Sum.elim_inl, decCy, Finset.mem_sdiff] at hb
      exact hb.1
    · refine ⟨_, gas_hSz (S₀ := S₀) m, fun b hb => ?_⟩
      simp only [gasCs, Sum.elim_inr, decZs, Finset.mem_sdiff] at hb
      exact hb.1
  exact decOp_pe_hole (latGraph_degree_le (d := S.d) (n := n k)) hop.hB0 hop.hκg hop.hκc le_rfl
    hop.hp hop.hκp (gas_hz hS₀) (fun X Cl h => gas_hnear hS₀ X Cl h)
    (fun X Φ => gasCoupling_empty C hv vc pres Y keptT X.1 e Φ) gas_hSx gas_hSz gas_hclx gas_hclz
    hop.hβd hop.hτd hop.hβm hop.hτm hop.hτi hop.hB hzd hG3 hop.hK0g hop.hent hop.hK1 hop.hcount
    hop.hh hop.hq hop.hcond

omit [NeZero S.L] in
/-- **The hole of a removal-free kept history lies in its kept region** (the hypothesis `hS₀` of
`gasP_pe` for `Kc = keptConfig 𝔸′`, `S₀ = holeOf 𝔸′`): a cube of `Y_k = Z^pre_k` lies in a component
of `Z^pre_k`, a member of the configuration. -/
theorem holeOf_sub_kept (hkK : k ≤ K) (A : LabHist S n R k0 K) (hrem : A.H.rem k = ∅) :
    ∀ b ∈ holeOf A, ∃ m ∈ (keptConfig M k A).members, b ∈ m.1 := by
  intro b hb
  rw [keptConfig_members hkK]
  have hbZ : b ∈ (A.H.step k).Z := (Finset.mem_filter.mp hb).2.2
  rw [A.H.Z_eq k, hrem] at hbZ
  simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.sdiff_empty] at hbZ
  have hbZp : b ∈ A.H.F.Zp k := by rw [← Finset.mem_coe, coe_finOf]; exact hbZ
  obtain ⟨Y, hY, hbY⟩ := mem_comp_self (ω := S.omega k) hbZp
  exact ⟨(Y, A.H.localHistory M K k ⟨Y, hY⟩), mem_configMembers.mpr ⟨⟨Y, hY⟩, rfl⟩, hbY⟩

/-! ### Inhabitation of `GasHop` -/

variable (rep) in
/-- The trivial presentation: one point per cube, no removed weight. -/
def trivPres : RemPres rep where
  Ω := fun _ => Unit
  μ := fun _ => Measure.dirac ()
  w := fun _ _ _ => 0
  fld := fun _ e _ => (e.1, e.2.1)
  a₁ := 0
  ν := 0
  rho := 0

/-- **`GasHop` is satisfiable** (rule 10): for the trivial presentation (all removed weights `0`)
the analytic clauses of (H-op) hold for suitable constants. -/
theorem exists_gasHop_trivPres (Kc : HistConfig S n R k0 K M k) (C : SFCtx S n R M K N k m₁ ϱ)
    (hv : EuclideanSpace ℝ (Fin N)) (vc : Def7v2.CorrCoef S.d) (Y : Set (Torus S.d (n k)))
    (S₀ : Finset (Torus S.d (n k))) (keptT : Finset (Torus S.d (n k)) → BExt S n M K N → ℂ)
    (e : BExt S n M K N) :
    ∃ hc : HopConsts, GasHop Kc C hv vc (trivPres rep) Y S₀ keptT e hc := by
  set Q : ℝ := ((2 * S.d : ℕ) : ℝ) ^ 2 * 2 ^ (2 * S.d + 1) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hQe : Q * Real.exp (-Q) < 1 := by
    have h1 : Q + 1 ≤ Real.exp Q := Real.add_one_le_exp Q
    have h2 : Real.exp (-Q) * Real.exp Q = 1 := by rw [← Real.exp_add]; simp
    have h3 : 0 < Real.exp (-Q) := Real.exp_pos _
    nlinarith
  set α : ℝ := 3 * Real.exp (-0) * 2 ^ (2 * S.d + 1) * Real.exp (-Q) / (1 - Q * Real.exp (-Q))
    with hα
  have hα0 : 0 ≤ α := by
    have : 0 < 1 - Q * Real.exp (-Q) := by linarith
    positivity
  set κg : ℝ := 2 + 0 + α + Q with hκg
  set K0g : ℝ := (Fintype.card (DecObj (fun (X : LDom S n k) (Cl : RemCl rep Kc) =>
    gasNear rep Kc X.1 Cl)) : ℝ) with hK0g
  have hexp : -((κg - 2) - 0 - α) = -Q := by rw [hκg]; ring
  have hτ0 : ∀ (Cl : RemCl rep Kc) (Φ : ∀ b, (trivPres rep).Ω b),
      gasTau Kc (trivPres rep) Cl e Φ = 0 := by
    intro Cl Φ
    obtain ⟨m, hm⟩ := Finset.map_nonempty.mp Cl.2.nonempty
    unfold gasTau
    rw [Finset.prod_eq_zero hm rfl, mul_zero]
  have hsub : ∀ Φ Φ' : ∀ b, (trivPres rep).Ω b, Φ = Φ' := fun _ _ => funext fun _ => rfl
  refine ⟨⟨0, κg, κg, 0, α, 0, κg + 4, K0g, 1⟩, ?_⟩
  refine
    { prob := fun _ => by unfold trivPres; infer_instance
      hB0 := le_rfl
      hκg := by rw [hκg]; positivity
      hκc := le_rfl
      hp := le_rfl
      hκp := le_rfl
      hK0g := by rw [hK0g]; positivity
      hK1 := le_rfl
      hβd := fun _ Φ Φ' _ => by rw [hsub Φ Φ']
      hτd := fun _ Φ Φ' _ => by rw [hsub Φ Φ']
      hβm := fun _ => measurable_const' fun Φ Φ' => by rw [hsub Φ Φ']
      hτm := fun _ => measurable_const' fun Φ Φ' => by rw [hsub Φ Φ']
      hτi := fun Cl => by simp only [hτ0]; exact integrable_zero _ _ _
      hB := fun Γ _ y hy Φ hΦ => by
        exfalso
        obtain ⟨m, hm⟩ := y.2.1
        have hm' : m ∈ Γ.filter _ := hy ▸ hm
        exact hΦ m (Finset.mem_filter.mp hm').1 (hτ0 m Φ)
      hent := by
        unfold DecEnt
        intro Γ _ q
        dsimp only
        simp only [sub_self, neg_zero, zero_mul, Real.exp_zero, Finset.sum_const, nsmul_eq_mul,
          mul_one]
        rw [hK0g]
        exact_mod_cast Finset.card_le_univ _
      hcount := by
        unfold DecCount
        intro q v
        dsimp only
        simp only [hτ0, norm_zero, integral_zero, Finset.sum_const_zero, one_pow, one_mul]
        positivity
      hh := by
        dsimp only
        simp only [zero_mul, Real.exp_zero, mul_zero, zero_add, add_zero, mul_one, Real.log_one]
        linarith
      hq := by rw [hexp, ← hQ]; linarith [hQe]
      hcond := by rw [hexp, ← hQ] }

end Balaban.LargeField.G0
