/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.G0Expand

/-!
# G0: the convergence of the expansion of the decorated gas (the engine of G1, G3, G4)

P7 (3.27)–(3.28), printed p. 528; LFR Lemma III.10.5 (`notes/phase1/LF-RECONSTRUCTION.md`
§III.10.3): under the hypotheses (H-op), the expected partition function of the decorated gas of
removed clusters is `exp Σ_X P(X)`, the local terms `P(X)` localized on the *full* supports `X`
(the boundary domains of `ℬ′`, the polymers of `ℛ″`), with the weighted bound
`Σ_{X ∋ b} |P(X)| e^{κ_p steiner(X ∖ S₀)} ≤ α` at every cube `b` outside the hole.

* `pe_hole_full`: the polymer expansion with a hole (`pe_hole`) with the local terms localized on
  the full supports of the hole polymers: `logSeries = Σ_X P_full(X)` and the weighted bound at the
  cubes outside the hole (the clusters through such a cube are those of `pe_hole`);
* `actGasXi_decAct`: the partition function of the activation rule `decAct` is the decorated
  partition function `Σ_Γ ∏ τ · exp Σ_X b_X(Γ_X)` (P7 (3.26), `b_X(∅) = 0`);
* `decOp_pe_hole`: the engine: `E[Σ_Γ ∏ τ e^{Σ_X b_X(Γ_X)}] = exp Σ_X decP X` and the weighted bound
  of `decP`, from `actGasOp_pe_hole` (B2's activation-rule gas with a hole) and `pe_hole_full`.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset MeasureTheory Balaban.Polymer

namespace Balaban.LargeField.G0

/-! ### The polymer expansion with a hole, localized on the full supports -/

section Full

variable {B : Type*} [Fintype B] {H : SimpleGraph B} {S₀ : Finset B}

omit [Fintype B] in
/-- The charged union of a cluster of hole polymers is its full union minus the hole. -/
theorem unionOf_full_sdiff {n : ℕ} (X : Fin (n + 1) → HolePolymer H S₀) :
    unionOf (fun Y : HolePolymer H S₀ => Y.1) X \ S₀ = unionOf (holeSupp H S₀) X := by
  ext b
  simp only [unionOf, holeSupp, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, hi⟩, hb⟩
    exact ⟨i, hi, hb⟩
  · rintro ⟨i, hi, hb⟩
    exact ⟨⟨i, hi⟩, hb⟩

variable {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ) {ε κ κ' α : ℝ}

include hdeg in
/-- **The polymer expansion with a hole, localized on the full supports.**  Under the hypotheses of
`pe_hole` (activities of the hole polymers bounded by `ε e^{-κ steiner(X ∖ S₀)}`), the logarithm is
the sum of the local terms `P_full(X)` (clusters whose union of full supports is `X`), and at every
cube `b` outside the hole `Σ_{X ∋ b} |P_full(X)| e^{κ' steiner(X ∖ S₀)} ≤ α`. -/
theorem pe_hole_full (hε : 0 ≤ ε) (hκ' : 0 ≤ κ')
    (hq : (Δ : ℝ) ^ 2 * 2 ^ (Δ + 1) * Real.exp (-(κ - κ' - α)) < 1)
    (hcond : ε * 2 ^ (Δ + 1) * Real.exp (-(κ - κ' - α)) /
      (1 - (Δ : ℝ) ^ 2 * 2 ^ (Δ + 1) * Real.exp (-(κ - κ' - α))) ≤ α)
    (K : HolePolymer H S₀ → ℂ)
    (hK : ∀ X, ‖K X‖ ≤ ε * Real.exp (-κ * (steiner H (holeSupp H S₀ X) : ℝ))) :
    logSeries (shareBlock (holeSupp H S₀)) K =
      ∑ X : Finset B, PY (shareBlock (holeSupp H S₀)) (fun Y : HolePolymer H S₀ => Y.1) K X ∧
    ∀ b ∉ S₀, ∑ X ∈ (Finset.univ : Finset (Finset B)).filter (fun X => b ∈ X),
        ‖PY (shareBlock (holeSupp H S₀)) (fun Y : HolePolymer H S₀ => Y.1) K X‖ *
          Real.exp (κ' * (steiner H (X \ S₀) : ℝ)) ≤ α := by
  have hα : 0 ≤ α := by
    refine le_trans ?_ hcond
    have : 0 < 1 - (Δ : ℝ) ^ 2 * 2 ^ (Δ + 1) * Real.exp (-(κ - κ' - α)) := by linarith
    positivity
  set s : HolePolymer H S₀ → ℝ := fun X => (steiner H (holeSupp H S₀ X) : ℝ) with hs_def
  set g : Finset B → ℝ := fun Y => κ' * (steiner H Y : ℝ) with hg_def
  have hs : ∀ X, ((holeSupp H S₀ X).card : ℝ) ≤ s X := fun X => by
    show ((holeSupp H S₀ X).card : ℝ) ≤ (steiner H (holeSupp H S₀ X) : ℝ)
    exact_mod_cast card_le_steiner (exists_animal_of_holePolymer X)
  have hgs : ∀ X, g (holeSupp H S₀ X) ≤ κ' * s X := fun X => le_rfl
  have hent := entropy_hole (S₀ := S₀) hdeg hε hq hcond
  have hKP := sized_kp (holeSupp H S₀) s g hε hα hs hgs hent
  have hK' : ∀ X, ‖K X‖ ≤ sizedW (holeSupp H S₀) s g ε κ X := fun X => by
    refine (hK X).trans ?_
    unfold sizedW
    calc ε * Real.exp (-κ * s X) = ε * Real.exp (-κ * s X) * 1 := by rw [mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_le_exp (by
          have : 0 ≤ (steiner H (holeSupp H S₀ X) : ℝ) := Nat.cast_nonneg _
          simp only [hg_def, add_zero]; positivity)) (by positivity)
  refine ⟨logSeries_eq_sum_PY _ _ hKP K hK', fun b hb => ?_⟩
  have hG3 : ∀ (n : ℕ) (X : Fin (n + 1) → HolePolymer H S₀),
      (clusterGraph (shareBlock (holeSupp H S₀)) X).Connected →
      κ' * (steiner H (unionOf (fun Y : HolePolymer H S₀ => Y.1) X \ S₀) : ℝ) ≤
        ∑ i, κ' * (steiner H ((X i).1 \ S₀) : ℝ) + 0 * n := by
    intro n X hconn
    rw [unionOf_full_sdiff]
    have hsum := steiner_union_le (H := H) (fun i => holeSupp H S₀ (X i))
      (fun i => exists_animal_of_holePolymer (X i)) (clusterGraph (shareBlock (holeSupp H S₀)) X)
      hconn (fun i j hij => (lnk_shareBlock _ _ _).mp (clusterGraph_adj _ _ i j |>.mp hij).2)
    calc κ' * (steiner H (unionOf (holeSupp H S₀) X) : ℝ)
        ≤ κ' * ((∑ i, steiner H (holeSupp H S₀ (X i)) : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hsum) hκ'
      _ = ∑ i, κ' * (steiner H ((X i).1 \ S₀) : ℝ) := by
          push_cast; rw [Finset.mul_sum]; rfl
      _ ≤ _ := by simp
  have hbound := pe_PY_bound (shareBlock (holeSupp H S₀)) (fun Y : HolePolymer H S₀ => Y.1)
    (fun Y => κ' * (steiner H (Y \ S₀) : ℝ)) 0 le_rfl (fun Y => by positivity) hG3
    (κ0 := fun X => ε * Real.exp (-κ * s X)) (κ := sizedW (holeSupp H S₀) s g ε κ)
    (fun X => rfl) hKP K hK b
  refine hbound.trans ?_
  calc ∑ X : HolePolymer H S₀, (if b ∈ X.1 then sizedW (holeSupp H S₀) s g ε κ X *
        Real.exp (α * ((holeSupp H S₀ X).card : ℝ)) else 0)
      ≤ ∑ X : HolePolymer H S₀, (if b ∈ holeSupp H S₀ X then
          ε * Real.exp ((κ' + α - κ) * s X) else 0) := by
        refine Finset.sum_le_sum (fun X _ => ?_)
        have hiff : b ∈ X.1 ↔ b ∈ holeSupp H S₀ X := by
          simp only [holeSupp, Finset.mem_sdiff]; exact ⟨fun h => ⟨h, hb⟩, fun h => h.1⟩
        by_cases hbX : b ∈ X.1
        · have h2 : b ∈ holeSupp H S₀ X := hiff.mp hbX
          simp only [hbX, h2, ↓reduceIte]
          exact sizedW_mul_exp_le (holeSupp H S₀) s g hε hα hs hgs X
        · have h2 : b ∉ holeSupp H S₀ X := fun h => hbX (hiff.mpr h)
          simp only [hbX, h2, ↓reduceIte, le_refl]
    _ ≤ α := hent b

end Full

/-! ### The decorated gas as a gas with an activation rule -/

section Decor

variable {B Zt Xt : Type*} [Fintype B] [Fintype Zt] [Fintype Xt]

omit [Fintype B] in
/-- **The active decorated couplings of a family `Γ` are the domains meeting `Γ`**: the sum of the
couplings `b_X(S)` over the decorations active for `Γ` is `Σ_X b_X(Γ_X)` when `b_X(∅) = 0`. -/
theorem sum_decAct (near : Xt → Zt → Prop) (b : Xt → Finset Zt → ℂ) (hb0 : ∀ x, b x ∅ = 0)
    (Γ : Finset Zt) :
    ∑ y ∈ Finset.univ.filter (fun y : DecObj near => decAct near y Γ), b y.1.1 y.1.2 =
      ∑ x, b x (Γ.filter (near x)) := by
  rw [← Finset.sum_filter_of_ne (p := fun x => (Γ.filter (near x)).Nonempty)]
  · refine Finset.sum_bij' (fun y _ => y.1.1)
      (fun x hx => (⟨(x, Γ.filter (near x)), (Finset.mem_filter.1 hx).2,
        fun m hm => (Finset.mem_filter.1 hm).2⟩ : DecObj near)) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      have hy' : y.1.2 = Γ.filter (near y.1.1) := (Finset.mem_filter.1 hy).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [← hy']
      exact y.2.1
    · intro x _
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
    · intro y hy
      have hy' : y.1.2 = Γ.filter (near y.1.1) := (Finset.mem_filter.1 hy).2
      exact Subtype.ext (Prod.ext rfl hy'.symm)
    · intro x _
      rfl
    · intro y hy
      have hy' : y.1.2 = Γ.filter (near y.1.1) := (Finset.mem_filter.1 hy).2
      exact congrArg (b y.1.1) hy'
  · intro x _ hx
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    exact hx (by rw [hne, hb0])

omit [Fintype B] in
/-- **The partition function of the decorated gas** (P7 (3.26)): the gas with the activation rule
`decAct` has the partition function `Σ_Γ ∏_{m ∈ Γ} τ_m · exp Σ_X b_X(Γ_X)` (`b_X(∅) = 0`). -/
theorem actGasXi_decAct (zs : Zt → Finset B) (near : Xt → Zt → Prop) (b : Xt → Finset Zt → ℂ)
    (τ : Zt → ℂ) (hb0 : ∀ x, b x ∅ = 0) :
    actGasXi (decAct near) zs (fun y : DecObj near => b y.1.1 y.1.2) τ =
      ∑ Γ ∈ Finset.univ.filter
          (fun Γ : Finset Zt => ∀ m ∈ Γ, ∀ m' ∈ Γ, m ≠ m' → Disjoint (zs m) (zs m')),
        (∏ m ∈ Γ, τ m) * Complex.exp (∑ x, b x (Γ.filter (near x))) := by
  unfold actGasXi
  refine Finset.sum_congr rfl fun Γ _ => ?_
  rw [sum_decAct near b hb0 Γ]

omit [Fintype B] [Fintype Zt] [Fintype Xt] in
/-- The activation rule `decAct` reads only the heavy objects in contact with the coupling, when a
heavy object met by the domain is in contact with it. -/
theorem decAct_loc (S₀ : Finset B) (czF : Zt → Finset B) (cxF : Xt → Finset B)
    (near : Xt → Zt → Prop) (hnear : ∀ x m, near x m → ¬ Disjoint (cxF x \ S₀) (czF m \ S₀))
    (y : DecObj near) (Γ : Finset Zt) :
    decAct near y Γ ↔ decAct near y
      (Γ.filter (fun m => ¬ Disjoint (decCy S₀ czF cxF near y) (decZs S₀ czF m))) := by
  unfold decAct
  have hsub : ∀ m, near y.1.1 m → ¬ Disjoint (decCy S₀ czF cxF near y) (decZs S₀ czF m) := by
    intro m hm hd
    refine hnear y.1.1 m hm (Finset.disjoint_of_subset_left ?_ hd)
    unfold decCy decCyF
    exact Finset.sdiff_subset_sdiff Finset.subset_union_left le_rfl
  rw [Finset.filter_filter]
  have : Γ.filter (fun m => ¬ Disjoint (decCy S₀ czF cxF near y) (decZs S₀ czF m) ∧ near y.1.1 m) =
      Γ.filter (near y.1.1) :=
    Finset.filter_congr fun m _ => ⟨fun h => h.2, fun h => ⟨hsub m h, h⟩⟩
  rw [this]

omit [Fintype B] [Fintype Zt] [Fintype Xt] in
/-- An active decorated coupling meets a selected heavy object. -/
theorem decAct_meet (S₀ : Finset B) (czF : Zt → Finset B) (cxF : Xt → Finset B)
    (near : Xt → Zt → Prop) (hnear : ∀ x m, near x m → ¬ Disjoint (cxF x \ S₀) (czF m \ S₀))
    (y : DecObj near) (Γ : Finset Zt) (h : decAct near y Γ) :
    ∃ m ∈ Γ, ¬ Disjoint (decCy S₀ czF cxF near y) (decZs S₀ czF m) := by
  obtain ⟨m, hm⟩ := y.2.1
  have hm' : m ∈ Γ.filter (near y.1.1) := h ▸ hm
  refine ⟨m, (Finset.mem_filter.1 hm').1, fun hd => hnear y.1.1 m (Finset.mem_filter.1 hm').2
    (Finset.disjoint_of_subset_left ?_ hd)⟩
  unfold decCy decCyF
  exact Finset.sdiff_subset_sdiff Finset.subset_union_left le_rfl

end Decor

/-! ### The engine -/

/-! ### Named forms of the decidability-carrying statements -/

section Forms

variable {B Zt Xt : Type*} [Fintype B] [Fintype Zt] [Fintype Xt]
  {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]

/-- **The expected partition function of the decorated gas** (P7 (3.26)):
`E[Σ_Γ ∏_{m ∈ Γ} τ_m e^{Σ_X b_X(Γ_X)}]`, the families `Γ` of heavy objects with pairwise disjoint
charged supports. -/
def decXi (S₀ : Finset B) (czF : Zt → Finset B) (near : Xt → Zt → Prop)
    (τ : Zt → (∀ b, Ω b) → ℂ) (bc : Xt → Finset Zt → (∀ b, Ω b) → ℂ) (μ : ∀ b, Measure (Ω b)) :
    ℂ :=
  ∫ Φ, ∑ Γ ∈ Finset.univ.filter (fun Γ : Finset Zt =>
      ∀ m ∈ Γ, ∀ m' ∈ Γ, m ≠ m' → Disjoint (decZs S₀ czF m) (decZs S₀ czF m')),
    (∏ m ∈ Γ, τ m Φ) * Complex.exp (∑ x, bc x (Γ.filter (near x)) Φ) ∂(Measure.pi μ)

/-- The weighted sum of local terms through the cube `q`:
`Σ_{X ∋ q} |P(X)| e^{κ_p steiner(X ∖ S₀)}`. -/
def kpSum (H : SimpleGraph B) (S₀ : Finset B) (κp : ℝ) (Pf : Finset B → ℂ) (q : B) : ℝ :=
  ∑ X ∈ (Finset.univ : Finset (Finset B)).filter (fun X => q ∈ X),
    ‖Pf X‖ * Real.exp (κp * (steiner H (X \ S₀) : ℝ))

/-- The number of cubes outside the hole. -/
def chargedCard (S₀ : Finset B) : ℕ := (Finset.univ \ S₀).card

/-- **The entropy of the active couplings** (the hypothesis `hent` of `actGasOp_pe_hole` for the
decorated gas). -/
def DecEnt (H : SimpleGraph B) (S₀ : Finset B) (czF : Zt → Finset B) (cxF : Xt → Finset B)
    (near : Xt → Zt → Prop) (κ'' κg K0g : ℝ) : Prop :=
  ∀ Γ : Finset Zt, (∀ m ∈ Γ, ∀ m' ∈ Γ, m ≠ m' → Disjoint (decZs S₀ czF m) (decZs S₀ czF m')) →
    ∀ q : B, ∑ y ∈ Finset.univ.filter
        (fun y => decAct near y Γ ∧ q ∈ decCy S₀ czF cxF near y),
      Real.exp (-(κ'' - κg) * (steiner H (decCy S₀ czF cxF near y) : ℝ)) ≤ K0g

/-- **The weighted counts of the heavy weights** (the hypothesis `hcount` of `actGasOp_pe_hole`):
`Σ_{m ∋ q, |m| = v} E|τ_m| ≤ K₀ᵛ e^{-p - h v}`. -/
def DecCount (S₀ : Finset B) (czF : Zt → Finset B) (τ : Zt → (∀ b, Ω b) → ℂ)
    (μ : ∀ b, Measure (Ω b)) (K0h p h : ℝ) : Prop :=
  ∀ (q : B) (v : ℕ),
    ∑ m ∈ Finset.univ.filter (fun m => q ∈ decZs S₀ czF m ∧ (decZs S₀ czF m).card = v),
      ∫ Φ, ‖τ m Φ‖ ∂(Measure.pi μ) ≤ K0h ^ v * Real.exp (-p - h * v)

end Forms

section Engine

variable {B Zt Xt : Type*} [Fintype B] [Fintype Zt] [Fintype Xt]
  {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)] {μ : ∀ b, Measure (Ω b)}
  [∀ b, IsProbabilityMeasure (μ b)]
  {H : SimpleGraph B} {S₀ : Finset B} {czF : Zt → Finset B} {cxF : Xt → Finset B}
  {near : Xt → Zt → Prop} {τ : Zt → (∀ b, Ω b) → ℂ} {bc : Xt → Finset Zt → (∀ b, Ω b) → ℂ}
  {B0 κ'' c c2 p h : ℝ}

/-- **The convergence of the expansion of the decorated gas** (P7 (3.27)–(3.28); LFR Lemma III.10.5
under (H-op)).  Let the heavy weights `τ_m` and the couplings `b_X(S)` depend on the internal
configuration through the charged supports, the full supports be connected and closed under the
hole, a domain meeting a heavy object be in charged contact with it, `b_X(∅) = 0`, and the bounds of
`actGasOp_pe_hole` hold (sup bound of the active couplings, integrated weighted counts of the heavy
weights, entropy of the active couplings, the PE inequalities).  Then
`E[Σ_Γ ∏_{m ∈ Γ} τ_m e^{Σ_X b_X(Γ_X)}] = exp Σ_X P(X)` with `P = decP` localized on the full
supports, `Σ_{X ∋ b} |P(X)| e^{κ_p steiner(X ∖ S₀)} ≤ α` at every cube `b` outside the hole, and
`|Σ_X P(X)| ≤ |𝕋 ∖ S₀| α`. -/
theorem decOp_pe_hole {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ) {κg κp α : ℝ}
    (hB0 : 0 ≤ B0) (hκg : 0 ≤ κg) (hκ'' : κg ≤ κ'') (hc : 0 ≤ c) (hp : 0 ≤ p) (hκp : 0 ≤ κp)
    (hz : ∀ m, (decZs S₀ czF m).Nonempty)
    (hnear : ∀ x m, near x m → ¬ Disjoint (cxF x \ S₀) (czF m \ S₀))
    (hb0 : ∀ x Φ, bc x ∅ Φ = 0)
    (hSx : ∀ y : DecObj near, IsAnimal H (decCyF czF cxF near y))
    (hSz : ∀ m, IsAnimal H (czF m))
    (hclx : ∀ y : DecObj near, HoleClosed H S₀ (decCyF czF cxF near y))
    (hclz : ∀ m, HoleClosed H S₀ (czF m))
    (hβd : ∀ y, DepOn (decCy S₀ czF cxF near y) (decβ near bc y))
    (hτd : ∀ m, DepOn (decZs S₀ czF m) (τ m))
    (hβm : ∀ y, Measurable (decβ near bc y)) (hτm : ∀ m, Measurable (τ m))
    (hτi : ∀ m, Integrable (τ m) (Measure.pi μ))
    (hB : ∀ Γ : Finset Zt,
      (∀ m ∈ Γ, ∀ m' ∈ Γ, m ≠ m' → Disjoint (decZs S₀ czF m) (decZs S₀ czF m')) →
      ∀ y, decAct near y Γ → ∀ Φ, (∀ m ∈ Γ, τ m Φ ≠ 0) →
        ‖decβ near bc y Φ‖ ≤ B0 * Real.exp (-κ'' * (steiner H (decCy S₀ czF cxF near y) : ℝ)))
    (hzd : ∀ m, (steiner H (decZs S₀ czF m) : ℝ) ≤ c2 * (decZs S₀ czF m).card)
    (hG3 : ∀ C : Finset (DecObj near ⊕ Zt),
      ConnSet (gasCs (decCy S₀ czF cxF near) (decZs S₀ czF)) C →
      actGasA (decAct near) (decZs S₀ czF) C →
      (steiner H (unionCs (gasCs (decCy S₀ czF cxF near) (decZs S₀ czF)) C) : ℝ) ≤
        ∑ t ∈ C, (steiner H (gasCs (decCy S₀ czF cxF near) (decZs S₀ czF) t) : ℝ) +
          c * ((C.card : ℝ) - 1))
    {K0g K0h : ℝ} (hK0g : 0 ≤ K0g) (hent : DecEnt H S₀ czF cxF near κ'' κg K0g)
    (hK1 : 1 ≤ K0h) (hcount : DecCount S₀ czF τ μ K0h p h)
    (hh : B0 * Real.exp B0 * Real.exp (κg * c) * K0g + κg * (c2 + c) + 1 + 3 + Real.log K0h ≤ h)
    (hq : (Δ : ℝ) ^ 2 * 2 ^ (Δ + 1) * Real.exp (-((κg - 2) - κp - α)) < 1)
    (hcond : 3 * Real.exp (-p) * 2 ^ (Δ + 1) * Real.exp (-((κg - 2) - κp - α)) /
      (1 - (Δ : ℝ) ^ 2 * 2 ^ (Δ + 1) * Real.exp (-((κg - 2) - κp - α))) ≤ α) :
    decXi S₀ czF near τ bc μ = Complex.exp (∑ X : Finset B, decP H S₀ czF cxF near τ bc μ X) ∧
    (∀ q ∉ S₀, kpSum H S₀ κp (decP H S₀ czF cxF near τ bc μ) q ≤ α) ∧
    ‖∑ X : Finset B, decP H S₀ czF cxF near τ bc μ X‖ ≤ (chargedCard S₀ : ℝ) * α := by
  unfold DecEnt at hent
  unfold DecCount at hcount
  have hloc := decAct_loc S₀ czF cxF near hnear
  have hmeet := decAct_meet S₀ czF cxF near hnear
  have hS : ∀ t, IsAnimal H (gasCs (decCyF czF cxF near) czF t) := fun t => by
    rcases t with y | m
    · exact hSx y
    · exact hSz m
  have hcl : ∀ t, HoleClosed H S₀ (gasCs (decCyF czF cxF near) czF t) := fun t => by
    rcases t with y | m
    · exact hclx y
    · exact hclz m
  obtain ⟨hXi, hexp, -, -, hlog, -, -⟩ := actGasOp_pe_hole (cyF := decCyF czF cxF near) (zsF := czF)
    hdeg hB0 hκg hκ'' hc hp hκp hz hloc hmeet (fun _ => rfl) (fun _ => rfl) hS hcl hβd hτd hβm
    hτm hτi hB hzd hG3 hK0g hent hK1 hcount hh hq hcond
  have hd : ∀ Y : Finset B, 0 ≤ (steiner H Y : ℝ) := fun Y => Nat.cast_nonneg _
  have hK : ∀ X : HolePolymer H S₀, ‖decHoleK H S₀ czF cxF near τ bc μ X‖ ≤
      3 * Real.exp (-p) * Real.exp (-(κg - 2) * (steiner H (holeSupp H S₀ X) : ℝ)) := by
    intro X
    have := norm_actGasHoleKOp_le (cyF := decCyF czF cxF near) (zsF := czF)
      (d := fun Y : Finset B => (steiner H Y : ℝ)) (c1 := 1) hB0 hκg hκ'' hc zero_le_one hp hd hz
      hmeet hτd hβm hτm hτi hB hzd hG3 hK0g hent hK1 hcount hh X
      (by
        have h1 := card_le_steiner (exists_animal_of_holePolymer X)
        have h2 : ((holeSupp H S₀ X).card : ℝ) ≤ (steiner H (holeSupp H S₀ X) : ℝ) := by
          exact_mod_cast h1
        simp only [one_mul]
        linarith)
    unfold decHoleK
    simpa [mul_assoc] using this
  obtain ⟨hsum, hbd⟩ := pe_hole_full hdeg (by positivity : (0 : ℝ) ≤ 3 * Real.exp (-p)) hκp hq
    hcond (decHoleK H S₀ czF cxF near τ bc μ) hK
  have hpt : ∀ Φ : ∀ b, Ω b,
      actGasXi (decAct near) (decZs S₀ czF) (fun y => decβ near bc y Φ) (fun m => τ m Φ) =
        ∑ Γ ∈ Finset.univ.filter (fun Γ : Finset Zt =>
          ∀ m ∈ Γ, ∀ m' ∈ Γ, m ≠ m' → Disjoint (decZs S₀ czF m) (decZs S₀ czF m')),
          (∏ m ∈ Γ, τ m Φ) * Complex.exp (∑ x, bc x (Γ.filter (near x)) Φ) := fun Φ =>
    actGasXi_decAct (decZs S₀ czF) near (fun x S => bc x S Φ) (fun m => τ m Φ) (fun x => hb0 x Φ)
  refine ⟨?_, hbd, ?_⟩
  · calc decXi S₀ czF near τ bc μ
        = actGasXiOp (decAct near) (decZs S₀ czF) (decβ near bc) τ μ := by
          unfold decXi
          unfold actGasXiOp
          exact integral_congr_ae (Filter.Eventually.of_forall fun Φ => (hpt Φ).symm)
      _ = Complex.exp (logSeries (shareBlock (holeSupp H S₀))
            (decHoleK H S₀ czF cxF near τ bc μ)) := hXi.trans hexp
      _ = Complex.exp (∑ X : Finset B, decP H S₀ czF cxF near τ bc μ X) := by
          rw [hsum]
          rfl
  · rw [show (∑ X : Finset B, decP H S₀ czF cxF near τ bc μ X) =
        logSeries (shareBlock (holeSupp H S₀)) (decHoleK H S₀ czF cxF near τ bc μ) from hsum.symm]
    exact hlog

end Engine

end Balaban.LargeField.G0
