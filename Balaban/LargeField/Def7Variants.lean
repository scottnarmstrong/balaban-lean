module

public import Balaban.LargeField.Def7

/-!
# Def-7, variants: `IsRep^pre_k`, `IsRep^♭_k`, `IsRepFam_k` — DRAFT

LF-RECONSTRUCTION v1.3 §II.6.3 (the variants), Definition IV.3.1 (the family class, version 1.2,
replacing Definition II.6.4) and §II.6.5 (the external field `g` and the limit `ν ↓ 0`).

* `IsRepPre` (§II.6.3, first item; ARCH §3.6; Part III D-III.4): as `IsRep_k` with `Z^pre_k` in
  place of `Z_k` — no `R`-record at scale `k` (`IsComplete k k`, `D4Pin k`, `D5Bound k`), the
  operators `𝕋^pre_k` (`D1PreForm`), (H6′)^pre (`D6Pre`), (D7) with `κ_+ = 3κ/2` and `B_st`, and
  (D2) with the bound `½ β_k^{-m-1}` for `ℛ^{(k)}_m`.
* `IsRepFlat` (§II.6.3, second item; `k₀ ≤ k ≤ k_f`): no `R`-records beyond `k₀` (built into the
  landed `RegionHistory.rem_empty`), complete backgrounds above `k₀` (`FieldClauses.mu_eq`),
  (D2♭) (`SFFlat`: Def-6 with the mass range `0 < ν_k ≤ 1`), (D9♭) (`D9Flat`) and (H6♭)
  (`D6Flat`, with the a priori horizon `k̂_f`).
* `IsRepFam`, `IsRepFamPre` (Definition IV.3.1): a family `ν ↦ (F(ν), ρ(ν))`,
  `0 < ν ≤ ν_*(k) = β^{-1} L^{-kd}`, each member on the tori of its `ν` (the regime index
  `k₀(ν) = kZero(β, ν)` and the horizon `K(ν)` vary with `ν`): (F-i) `IsRep_k` (resp.
  `IsRep^pre_k`) for every `ν`; the running constants have limits as `ν ↓ 0` (`runLim`); the
  small-field part of (F-iii): almost-everywhere limits of the terms `ℰ`, `ℳ`, `ℛ` on every
  Def-6 torus (`SFLimit`).  **Not formalized (open point):** (F-ii) and the large-field part
  of (F-iii), which are statements on the `ℤ^d` data of (D8) for the localized histories and their
  step, kept and boundary data; they need a transport of localized histories, variables and
  kernels between tori, which is not landed.

§II.6.5: items 1-4 (`g` an analytic parameter, entering the operators through `e^b` only, local,
with sup bounds on the polydisc) are built into the landed `LFKernel` (`analytic_b`, `real_b`),
`StepData.b_supp`, `KeptData.b_supp`, `KerBound` (all `g ∈ l1Ball`), into (D7) and into Def-6's
`analyticM` (the term `ℱ_k`); item 5 is `IsRepFam`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Def7

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory Filter Topology
open Balaban.SmallField

/-! ### The pre-`R` clauses -/

section Pre

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}

/-- The term `𝕋^pre_k(Z^pre_k(𝔸), 𝔸)[e^{ℬ^{(k)}(𝔸)} χ_k((Z^pre_k)^c) exp(𝒜_k + ℱ_k + ℛ^{(k)})]` of
the pre-`R` form (the components of `Z^pre_k`, the operators `𝕋^pre_k`). -/
noncomputable def preTerm {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) : ℂ :=
  gOp (fun c : A.H.Comp k => A.H.localHistory M K k c) k
    (preOpTop geo cs rep.SD rep.KD A k C.hkK) ψk hv g
    (integrand (fun c : A.H.Comp k => A.H.localHistory M K k c)
      (preOpTop geo cs rep.SD rep.KD A k C.hkK)
      (fun c => fineSet (S := S) (n := n) M K k (c.1 : Set (Torus S.d (n k)))) C rep A
      (A.H.F.Zpre k) ψk hv g)

/-- The integral of the pre-`R` term converges absolutely. -/
def PreConv {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) : Prop :=
  GConv (fun c : A.H.Comp k => A.H.localHistory M K k c) k
    (preOpTop geo cs rep.SD rep.KD A k C.hkK) ψk hv g
    (integrand (fun c : A.H.Comp k => A.H.localHistory M K k c)
      (preOpTop geo cs rep.SD rep.KD A k C.hkK)
      (fun c => fineSet (S := S) (n := n) M K k (c.1 : Set (Torus S.d (n k)))) C rep A
      (A.H.F.Zpre k) ψk hv g)

/-- **(D1) for `IsRep^pre_k`**: the form identity with `Z^pre_k` and the operators `𝕋^pre_k`. -/
def D1PreForm {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
    (rep : Rep S n R k0 K M N geo cs P k) (hv : EuclideanSpace ℝ (Fin N))
    (ρ : (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) → (GIdx S n M K N → ℂ) → ℂ) : Prop :=
  ∀ (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ),
    g ∈ l1Ball (GIdx S n M K N) →
      (∀ A ∈ rep.hist, PreConv C rep A ψk hv g) ∧
        ρ ψk g = ∑ A ∈ rep.hist, preTerm C rep A ψk hv g

/-- **(H6′)^pre** (§II.6.3; Part III D-III.4): every component `Z` of `Z^pre_k(𝔸)` (ripe
components allowed) satisfies `t^*(Z) ≥ k` and `G^pre_k(Z) ≥ τ_{t^*(Z)} + V_k(Z) + ν(Z) + U(Z)`. -/
def D6Pre (rep : Rep S n R k0 K M N geo cs P k) : Prop :=
  ∀ A ∈ rep.hist, ∀ c : A.H.Comp k,
    k ≤ S.tStar (A.H.bk k c) ∧
      S.tau (S.tStar (A.H.bk k c)) + 2 * S.sigma k * (A.H.bk k c).len +
          S.W (k + 1) (S.tStar (A.H.bk k c)) + (A.H.bk k c).nu + S.bank (A.H.bk k c) ≤
        rep.Gpre A k c

/-- **(H6♭)** (§II.6.3 (v); `k₀ ≤ k ≤ k_f`): every component of `Z_k(𝔸)` satisfies
`G_k(Z) ≥ A₂ λ̂_{k₀}^{p₂} + 2σ_k ℓ(Γ(Z)) + W_{k+1}(k̂_f)` (`khat` the a priori horizon `k̂_f`). -/
def D6Flat (khat : ℕ) (rep : Rep S n R k0 K M N geo cs P k) : Prop :=
  ∀ A ∈ rep.hist, ∀ c : PostComp A k,
    S.A2 * S.lam k0 ^ S.p2 + 2 * S.sigma k * (A.H.bk k c.1).len + S.W (k + 1) khat ≤
      rep.Gpost A k c.1

end Pre

/-! ### (D2♭), (D9♭) -/

section Flat

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- `Def6.Consts` with the bound `ν̄` of the mass replaced by `1` (the mass range of (D2♭)). -/
def massOne (P6 : Def6.Consts) : Def6.Consts := { P6 with νbar := 1 }

/-- **(D2♭)** (§II.6.3 (iii); audit P2-01): `𝔰` satisfies the clauses (H.1)-(H.7) of Def-6 at
scale `k` verbatim, with the mass range `0 < ν_k ≤ ν̄` of the "Space" clause replaced by
`0 < ν_k ≤ 1` (the coefficient bounds with `ν̄ := 1`; the constants themselves stay admissible),
and the `ℛ^{(k)}_n` satisfy P5 H4 as in (D2). -/
structure SFFlat (P6 : Def6.Consts) (sf : SFData d L m₁ k N ϱ) : Prop where
  admissible : P6.Admissible d L
  coeff : Def6.CoeffBounds d L k (massOne P6) sf.β sf.ν sf.a
  torus : ∃ ρsf : ∀ (N₁ : ℕ) [NeZero N₁], (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) →
      (Fin N → ℝ) → (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ,
    ∀ (N₁ : ℕ) [NeZero N₁], Def6.IsSF P6 sf.β sf.ν sf.a (sf.Tm N₁) (ρsf N₁) (sf.E N₁)
  torusIndep : Def6.TorusIndep P6.m₀ sf.Tm
  renorm : ∀ j, 1 ≤ j → j ≤ k → Def6.RenormCond (d := d) (L := L) (m₁ := m₁) (N := N)
    (ϱ := ϱ) P6.m₀ k (sf.ν k) sf.Tm j
  rTerms : ∀ (N₁ : ℕ) [NeZero N₁], RTermsH4 (ϱ := ϱ) P6 sf.β sf.ν sf.a N₁ (sf.Rt N₁) (fun _ => 1)

/-- **(D9♭)** (§II.6.3 (iv)): `β_k > B L^{k(d-2)}` and `0 < ν_k ≤ 1`. -/
structure D9Flat (P6 : Def6.Consts) (sf : SFData d L m₁ k N ϱ) : Prop where
  beta_gt : P6.B * (L : ℝ) ^ (k * (d - 2)) < sf.β k
  nu_pos : 0 < sf.ν k
  nu_le : sf.ν k ≤ 1

end Flat

/-! ### The variants -/

section Variants

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}

/-- The bound factors of `ℛ^{(k)}_n` for `IsRep^pre_k`: `½` for `n = m = m₀ + m₁`, `1` otherwise
(P5 Proposition 3.2: the bounds (3.4) with `½ β_k^{-m-1}`). -/
noncomputable def preFac (m : ℕ) : ℕ → ℝ := fun nn => if nn = m then 1 / 2 else 1

/-- **`IsRep^pre_k`** (§II.6.3, first item): as `IsRep_k` with `Z^pre_k` in place of `Z_k` (no
`R`-record at scale `k`, the operators `𝕋^pre_k`), (H6′)^pre in place of (D6), (D7) with
`κ_+ = 3κ/2` and `B_st` in place of `κ`, `B₀`, and (D2) with `½ β_k^{-m-1}` for `ℛ^{(k)}_m`. -/
structure IsRepPre (S : Setting) (R : ℕ → ℝ) (k0 K M : ℕ) [NeZero M] [NeZero S.L] (N : ℕ)
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M) (cs : OpConsts)
    (P : BudgetConsts) (P6 : Def6.Consts) (C7 : Consts7) (β ν : ℝ)
    (hv : EuclideanSpace ℝ (Fin N)) (k : ℕ) {ϱ : ℝ} (hM6 : M = S.L ^ (P6.m₀ + C7.m₁))
    (hkK : k ≤ K) (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ)
    (ρ : ∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L K nK) M K k → EuclideanSpace ℝ (Fin N)) →
      (GIdx S (sides S.L K nK) M K N → ℂ) → ℂ) : Prop where
  coh : Coh S R k0 M cs P P6 C7 β ν k F.sf
  field : FieldClauses S k0 k cs F.sf hv
  complete : ∀ (nK : ℕ) [NeZero nK], IsComplete k k (F.lf nK).hist
  form : ∀ (nK : ℕ) [NeZero nK], D1PreForm (F.ctx hM6 hkK nK) (F.lf nK) hv (ρ nK)
  sfData : D2SF P6 F.sf (preFac (P6.m₀ + C7.m₁))
  pin : ∀ (nK : ℕ) [NeZero nK], D4Pin k (F.lf nK)
  opBound : ∀ (nK : ℕ) [NeZero nK], D5Bound k hkK (F.lf nK)
  budget : ∀ (nK : ℕ) [NeZero nK], D6Pre (F.lf nK)
  bdry : ∀ (nK : ℕ) [NeZero nK], D7Bdry (sides_hnn S.L K nK) hkK (F.lf nK)
    (fun A => A.H.F.Zpre k) F.weights cs.mu (P6.eps S.d S.L) (epsOne S P6 C7) cs.nu C7.Bst
    (3 / 2 * P6.κ) hv
  coherent : D8SF P6.m₀ F.sf
  coeff : D9Coeff P6 k0 F.sf

/-- **`IsRep^♭_k`** (§II.6.3, second item; `k₀ ≤ k ≤ k_f`): as `IsRep_k` except (i) no
`R`-records at the scales `> k₀` (the landed histories have `Rem_j = ∅` for `j > k₀`), (ii) complete
backgrounds above `k₀` (`FieldClauses.mu_eq`), (iii) (D2♭), (iv) (D9♭), (v) (H6♭) with the a
priori horizon `khat = k̂_f`. -/
structure IsRepFlat (S : Setting) (R : ℕ → ℝ) (k0 K M : ℕ) [NeZero M] [NeZero S.L] (N : ℕ)
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M) (cs : OpConsts)
    (P : BudgetConsts) (P6 : Def6.Consts) (C7 : Consts7) (β ν : ℝ)
    (hv : EuclideanSpace ℝ (Fin N)) (k khat : ℕ) {ϱ : ℝ} (hM6 : M = S.L ^ (P6.m₀ + C7.m₁))
    (hkK : k ≤ K) (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ)
    (ρ : ∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L K nK) M K k → EuclideanSpace ℝ (Fin N)) →
      (GIdx S (sides S.L K nK) M K N → ℂ) → ℂ) : Prop where
  range : k0 ≤ k
  coh : Coh S R k0 M cs P P6 C7 β ν k F.sf
  field : FieldClauses S k0 k cs F.sf hv
  complete : ∀ (nK : ℕ) [NeZero nK], IsComplete k (k + 1) (F.lf nK).hist
  form : ∀ (nK : ℕ) [NeZero nK], D1Form (F.ctx hM6 hkK nK) (F.lf nK) hv (ρ nK)
  sfData : SFFlat P6 F.sf
  pin : ∀ (nK : ℕ) [NeZero nK], D4Pin (k + 1) (F.lf nK)
  opBound : ∀ (nK : ℕ) [NeZero nK], D5Bound (k + 1) hkK (F.lf nK)
  budget : ∀ (nK : ℕ) [NeZero nK], D6Flat khat (F.lf nK)
  bdry : ∀ (nK : ℕ) [NeZero nK], D7Bdry (sides_hnn S.L K nK) hkK (F.lf nK)
    (fun A => (A.H.step k).Z) F.weights cs.mu (P6.eps S.d S.L) (epsOne S P6 C7) cs.nu C7.B0 P6.κ hv
  coherent : D8SF P6.m₀ F.sf
  coeff : D9Flat P6 F.sf

/-- `ν_*(k) = β^{-1} L^{-kd}` (Definition IV.3.1). -/
noncomputable def nuStar (d L : ℕ) (β : ℝ) (k : ℕ) : ℝ := β⁻¹ * ((L : ℝ) ^ (k * d))⁻¹

section Fam

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **The limit `ν ↓ 0` of the small-field data** (Definition IV.3.1 (F-iii), small-field part:
"outside a Lebesgue-null set of values of its variables it has a limit as `ν ↓ 0`"), on the Def-6
torus `N₁`: in the variables `b = ν_j h`, for almost every value of the variables at which the
data lie in their analyticity domain for all small `ν`, the terms `ℰ^{(j)}(y, X)`, `ℳ^{(j)}(x, X)`
and `ℛ^{(k)}_n(X)` have limits.  (Def-6's `ContAtZero` is not used here: its
open set is now taken in the space of block-constant fields (`Def6.blockConstE`), where `XiDom`
has interior; this a.e. form is the Def-7 variant of the same clause.) -/
structure SFLimit (P6 : Def6.Consts) (N₁ : ℕ) [NeZero N₁] (sfν : ℝ → SFData d L m₁ k N ϱ) :
    Prop where
  limE : ∀ j y X, ∀ᵐ p : Def6.Fld d L N₁ m₁ k N × Def6.Fld d L N₁ m₁ k N,
    (∀ᶠ ν in 𝓝[>] 0, Def6.XiDom (((sfν ν).Tm N₁).gs j X) (Def6.aIdeal L k ((sfν ν).a k))
      (Def6.bgMass L k ((sfν ν).β k) ((sfν ν).ν k)) j (P6.eps d L j) p.1
      ((Def6.nuIdeal L k ((sfν ν).ν k) j)⁻¹ • p.2)) →
    ∃ l, Tendsto (fun ν => ((sfν ν).Tm N₁).E j y X p.1
      ((Def6.nuIdeal L k ((sfν ν).ν k) j)⁻¹ • p.2)) (𝓝[>] 0) (𝓝 l)
  limM : ∀ j x X (g : Def6.Fld d L N₁ m₁ k N), Def6.l1 g < 1 →
    ∀ᵐ p : Def6.Fld d L N₁ m₁ k N × Def6.Fld d L N₁ m₁ k N,
      (∀ᶠ ν in 𝓝[>] 0, Def6.XiDom (((sfν ν).Tm N₁).gs j X) (Def6.aIdeal L k ((sfν ν).a k))
        (Def6.bgMass L k ((sfν ν).β k) ((sfν ν).ν k)) j (P6.eps d L j) p.1
        ((Def6.nuIdeal L k ((sfν ν).ν k) j)⁻¹ • p.2)) →
      ∃ l, Tendsto (fun ν => ((sfν ν).Tm N₁).M j x X p.1
        ((Def6.nuIdeal L k ((sfν ν).ν k) j)⁻¹ • p.2) g) (𝓝[>] 0) (𝓝 l)
  limR : ∀ nn X (g : Def6.Fld d L N₁ m₁ k N), Def6.l1 g < 1 →
    ∀ᵐ p : Def6.Fld d L N₁ m₁ k N × Def6.Fld d L N₁ m₁ k N,
      (∀ᶠ ν in 𝓝[>] 0, Def6.XiDom (Def6.topGS d L N₁ m₁ k ϱ) (Def6.aIdeal L k ((sfν ν).a k))
        (Def6.bgMass L k ((sfν ν).β k) ((sfν ν).ν k)) k (P6.eps d L k) p.1
        (((sfν ν).ν k)⁻¹ • p.2)) →
      ∃ l, Tendsto (fun ν => (sfν ν).Rt N₁ nn X p.1 (((sfν ν).ν k)⁻¹ • p.2) g) (𝓝[>] 0) (𝓝 l)

/-- **The continuity clauses of the family class** (Definition IV.3.1, (F-iii) small-field part
and "the running constants have limits as `ν ↓ 0`"), for the small-field data `ν ↦ 𝔰(ν)`; the
bounds are uniform in `ν` because the constants of `IsRep` do not depend on `ν`. -/
structure FamCont (P6 : Def6.Consts) (sfν : ℝ → SFData d L m₁ k N ϱ) : Prop where
  runLim : ∀ j, j ≤ k → (∃ b, Tendsto (fun ν => (sfν ν).β j) (𝓝[>] 0) (𝓝 b)) ∧
    (∃ m, Tendsto (fun ν => (sfν ν).ν j) (𝓝[>] 0) (𝓝 m)) ∧
    (∃ z, Tendsto (fun ν => (sfν ν).z j) (𝓝[>] 0) (𝓝 z)) ∧
    (∃ a, Tendsto (fun ν => (sfν ν).a j) (𝓝[>] 0) (𝓝 a))
  vacLim : ∀ (N₁ : ℕ), ∃ e, Tendsto (fun ν => (sfν ν).E N₁) (𝓝[>] 0) (𝓝 e)
  sfLim : ∀ (N₁ : ℕ) [NeZero N₁], SFLimit P6 N₁ sfν

end Fam

/-- **`IsRepFam_k`** (Definition IV.3.1, version 1.2; D-IV.8): for fixed `β, h`, constants and
`k ≥ 1`, a family `ν ↦ (F(ν), ρ(ν))` for `0 < ν ≤ ν_*(k)`, each member with the regime index
`k₀(ν) = kZero(β, ν)` and on the tori of its horizon `K(ν) ≥ k`:
* `member` (F-i): `IsRep_k` for every `ν`;
* `cont`: the running constants have limits and the small-field part of (F-iii) holds.
(F-ii) and the large-field part of (F-iii) are not formalized (module docstring). -/
structure IsRepFam (S : Setting) (R : ℕ → ℝ) (M : ℕ) [NeZero M] [NeZero S.L] (N : ℕ)
    (Kν : ℝ → ℕ) (geo : ∀ (ν : ℝ) (nK : ℕ) [NeZero nK], Geo S (sides S.L (Kν ν) nK) R M)
    (cs : ℝ → OpConsts) (P : ℝ → BudgetConsts) (P6 : Def6.Consts) (C7 : Consts7) (β : ℝ)
    (hv : EuclideanSpace ℝ (Fin N)) (k : ℕ) {ϱ : ℝ} (hM6 : M = S.L ^ (P6.m₀ + C7.m₁))
    (hkK : ∀ ν, k ≤ Kν ν)
    (F : ∀ ν : ℝ, RepFam S R (kZero S.d S.L β ν) (Kν ν) M N (geo ν) (cs ν) (P ν) k C7.m₁ ϱ)
    (ρ : ∀ (ν : ℝ) (nK : ℕ) [NeZero nK],
      (BlockAt S (sides S.L (Kν ν) nK) M (Kν ν) k → EuclideanSpace ℝ (Fin N)) →
        (GIdx S (sides S.L (Kν ν) nK) M (Kν ν) N → ℂ) → ℂ) : Prop where
  member : ∀ ν, 0 < ν → ν ≤ nuStar S.d S.L β k →
    IsRep S R (kZero S.d S.L β ν) (Kν ν) M N (geo ν) (cs ν) (P ν) P6 C7 β ν hv k hM6 (hkK ν)
      (F ν) (ρ ν)
  cont : FamCont P6 (fun ν => (F ν).sf)

/-- **`IsRepFam^pre_k`** (Definition IV.3.1 for the pre-`R` class). -/
structure IsRepFamPre (S : Setting) (R : ℕ → ℝ) (M : ℕ) [NeZero M] [NeZero S.L] (N : ℕ)
    (Kν : ℝ → ℕ) (geo : ∀ (ν : ℝ) (nK : ℕ) [NeZero nK], Geo S (sides S.L (Kν ν) nK) R M)
    (cs : ℝ → OpConsts) (P : ℝ → BudgetConsts) (P6 : Def6.Consts) (C7 : Consts7) (β : ℝ)
    (hv : EuclideanSpace ℝ (Fin N)) (k : ℕ) {ϱ : ℝ} (hM6 : M = S.L ^ (P6.m₀ + C7.m₁))
    (hkK : ∀ ν, k ≤ Kν ν)
    (F : ∀ ν : ℝ, RepFam S R (kZero S.d S.L β ν) (Kν ν) M N (geo ν) (cs ν) (P ν) k C7.m₁ ϱ)
    (ρ : ∀ (ν : ℝ) (nK : ℕ) [NeZero nK],
      (BlockAt S (sides S.L (Kν ν) nK) M (Kν ν) k → EuclideanSpace ℝ (Fin N)) →
        (GIdx S (sides S.L (Kν ν) nK) M (Kν ν) N → ℂ) → ℂ) : Prop where
  member : ∀ ν, 0 < ν → ν ≤ nuStar S.d S.L β k →
    IsRepPre S R (kZero S.d S.L β ν) (Kν ν) M N (geo ν) (cs ν) (P ν) P6 C7 β ν hv k hM6 (hkK ν)
      (F ν) (ρ ν)
  cont : FamCont P6 (fun ν => (F ν).sf)

end Variants

end Balaban.LargeField.Def7
