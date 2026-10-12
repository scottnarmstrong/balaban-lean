module

public import Balaban.LargeField.Def7SmallField

/-!
# Def-7: the representation `rep = (𝔰, 𝔄, 𝔇, ℬ)` and the predicate `IsRep_k` — DRAFT

LF-RECONSTRUCTION v1.3 §II.6.1-§II.6.2 (Definitions II.6.1-II.6.2), on the landed objects:
finite-horizon histories (`RegionHistory S n R k₀ K`, `LabHist`), the localized operators `locOp`
with the step and kept data `StepData`, `KeptData` (Definition II.5.7), the bound (1.26)
(`KerBound`), the characteristic functions `chiK`, the H7 domain `H7Domain`, the budget
`budgetPost`, and the small-field class Def-6 (`Def6.IsSFFamily`).  Draft: unfrozen and editable.

* `Consts7`, `Coh`: the constants of Def-7 not carried by the landed bundles, and the coherence of
  the bundles with the running constants (a priori `λ̂`, radii, `k₀` of D-IV.11, …).
* `FieldClauses`, `hDomR`, `hSetB`, `sfActMass` (in `Def7SmallField`): **the external-field
  clauses, isolated for the open point Q13** (see the docstring of `FieldClauses`).
* `Rep`: the representation on one torus: `𝔄` (`hist`), `𝔇` (`SD`, `KD`, the kept exponents
  `κK`), `ℬ` (`B`); `RepFam`: the family over the admissible tori with the small-field data `𝔰`.
* `D1Form` … `D9Coeff`: the clauses (D1)-(D9); `IsRep`: Definition II.6.2; `RepClass`: `𝓡_k(𝖼)`.

The torus of the history with `n_K` top cubes has the cube tori `n_j = n_K L^{K-j}` (`sides`); the
horizon `K` is a typing parameter (`k ≤ K`, the flow takes `K = k̂_f + 1`), and a history *up to
scale `k`* is an `Agree`-class of `LabHist` (`Def7Hist`).

(D3) is built into (D1): the characteristic function there is `SFCtx.chiY`, the function of
Definition II.3.2 item 1.  (D4) is built into the types of `Rep.SD`, `Rep.KD` (the landed
`StepData`, `KeptData` *are* the data satisfying (S0)-(S3), indexed by localized histories, so
(S4) holds by construction); the field `D4Pin` pins the remaining derived objects (the step exponent
`κ^{(k)}` is `kappaStepLoc` by the type of `SD`; the exponent of the kept bound is `κ^pre_k`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Def7

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory
open Balaban.SmallField

/-! ### Constants, tori, coherence -/

/-- The constants of Def-7 not carried by the landed bundles `Setting` (`d, L, M, R_base, λ̂,
p₀, p₂, p_R, A₂, A₃, A'₃, C_R, c_v, …`), `Geo` (`M = c M₁`), `OpConsts`, `BudgetConsts`
(`c₁, c₂, H₀`) and `Def6.Consts` (`γ, α₁, κ, E₀, c₈, c₉, α₀, B, ν̄, p, m₀`) of the prefix
§I.1.4 up to row 15. -/
structure Consts7 where
  /-- `m₁` with `M = L^{m₀ + m₁}` (the Def-6 tori are `CTorus d L N₁ m₁ k`) -/
  m₁ : ℕ
  /-- `A₀` of `δ_j` and `p₀(β_j)` (Definition II.1.1) -/
  A0 : ℝ
  /-- `A₁` of `ε_{1,j}` -/
  A1 : ℝ
  /-- `B₀` of the boundary terms (D7) -/
  B0 : ℝ
  /-- `B_st`: the constant of the boundary terms created by a step (§II.6.3, `IsRepPre`) -/
  Bst : ℝ

/-- The cube tori `n_j = n_K L^{K - j}` of the admissible torus with `n_K` top cubes (side
`ℓ = M n_K L^K`; v1.2 (A-IV.3): `M L^{k̂_f + 1} ∣ ℓ` with `K = k̂_f + 1`). -/
def sides (L K nK : ℕ) : ℕ → ℕ := fun j => nK * L ^ (K - j)

instance sides.neZero (L K nK j : ℕ) [NeZero L] [NeZero nK] : NeZero (sides L K nK j) :=
  ⟨Nat.mul_ne_zero (NeZero.ne nK) (pow_ne_zero _ (NeZero.ne L))⟩

theorem sides_hnn (L K nK : ℕ) : ∀ i, i < K → sides L K nK i = L * sides L K nK (i + 1) := by
  intro i hi
  unfold sides
  rw [show K - i = (K - (i + 1)) + 1 by omega, pow_succ]
  ring

/-- The Def-6 torus of the torus `n` at scale `k`: `N₁ = L^{m₀} n_k`
(`N₁ L^{m₁} = M n_k` is the number of `k`-blocks per side). -/
def sfIdx (L m₀ : ℕ) (n : ℕ → ℕ) (k : ℕ) : ℕ := L ^ m₀ * n k

instance (L m₀ k : ℕ) (n : ℕ → ℕ) [NeZero L] [∀ j, NeZero (n j)] : NeZero (sfIdx L m₀ n k) :=
  ⟨Nat.mul_ne_zero (pow_ne_zero _ (NeZero.ne L)) (NeZero.ne (n k))⟩

theorem sfIdx_hT {S : Setting} {n : ℕ → ℕ} {R : ℕ → ℝ} {M : ℕ} (geo : Geo S n R M) {m₀ m₁ k : ℕ}
    (hM6 : M = S.L ^ (m₀ + m₁)) :
    sfIdx S.L m₀ n k * S.L ^ m₁ * S.L ^ k = geo.M1 * (geo.c * n k) * S.L ^ k := by
  unfold sfIdx
  have h : S.L ^ m₀ * S.L ^ m₁ = geo.c * geo.M1 := by
    rw [← pow_add]; exact hM6.symm.trans geo.hM
  calc S.L ^ m₀ * n k * S.L ^ m₁ * S.L ^ k = S.L ^ m₀ * S.L ^ m₁ * n k * S.L ^ k := by ring
    _ = geo.c * geo.M1 * n k * S.L ^ k := by rw [h]
    _ = geo.M1 * (geo.c * n k) * S.L ^ k := by ring

/-- **Coherence of the typing bundles with the running constants and the a priori data**
(§II.1, ruling 2, D-IV.2, D-IV.11): the cube side `M = S.M = L^{m₀ + m₁}`; the bookkeeping
sequence is the a priori `λ̂_j` and the radii are `R̂_j = R_base λ̂_j²`; `k₀` is the a priori
regime index `kZero(β, ν)`; the operators and the budget use the running constants of `𝔰`
(`β_j`, `z_j`, `ν_j`) and the derived tolerances `δ_j`, `p₀(β_j)` (Definition II.1.1). -/
structure Coh (S : Setting) [NeZero S.L] (R : ℕ → ℝ) (k0 M : ℕ) (cs : OpConsts)
    (P : BudgetConsts) (P6 : Def6.Consts) (C7 : Consts7) (β ν : ℝ) (k : ℕ) {N : ℕ} {ϱ : ℝ}
    (sf : SFData S.d S.L C7.m₁ k N ϱ) : Prop where
  M_eq : M = S.M
  M_pow : M = S.L ^ (P6.m₀ + C7.m₁)
  lam_eq : ∀ j, S.lam j = lamHat S.d S.L β cs.aKer j
  R_eq : ∀ j, R j = S.Rb * S.lam j ^ 2
  k0_eq : k0 = kZero S.d S.L β ν
  beta_cs : ∀ j, j ≤ k → cs.beta j = sf.β j
  beta_P : ∀ j, j ≤ k → P.beta j = sf.β j
  z_cs : ∀ j, j ≤ k → cs.z j = sf.z j
  nu_cs : ∀ j, j ≤ k → cs.nu j = sf.ν j
  delta_cs : ∀ j, j ≤ k → cs.delta j = deltaRun C7.A0 S.p0 cs.aKer sf.β j
  p0_cs : ∀ j, j ≤ k → cs.p0 j = pZero C7.A0 S.p0 cs.aKer sf.β j
  B0_cs : cs.B0 = C7.B0

/-! ### The external-field clauses (open point Q13) -/

/-- **The auxiliary complex domain of the external field `h` for the localized small-field terms
`ℛ^{(k)}_n` (D2)** under LFR v1.3: no restriction beyond the domain `Ξ^c_k` (as for the terms of
Def-6, `XiDom`).  Open point Q13 (`notes/QUESTIONS-ROLAND-2.md` item 13,
`notes/phase1/Q13-ANSWER-astra.md`): the pinned-field proposal replaces it by a fixed small complex
ball around the physical real unit field. -/
def hDomR (N : ℕ) : Set (Fin N → ℂ) := Set.univ

/-- **The external fields at which the boundary terms are required to be analytic on the H7
domain and bounded (D7)** under LFR v1.3: the physical field (the H7 domain, Definition II.3.5,
fixes `h` in the lifts).  Open point Q13: the pinned-field proposal asks analyticity in `h` on a
fixed small complex ball around it. -/
def hSetB {N : ℕ} (hv : EuclideanSpace ℝ (Fin N)) : Set (Fin N → ℂ) := {hC hv}

/-- **The external-field clauses — open point Q13.**  All clauses of Def-7 that fix how the
external field `h` and the masses enter are collected here, so that the change asked by Q13
(`notes/QUESTIONS-ROLAND-2.md` item 13; `notes/phase1/Q13-ANSWER-astra.md`: a pinned-field domain,
`h` in a fixed small complex ball around the real unit vector, physical mass kept in the action,
background mass zero in the solver below `k₀`) is local to this structure, `hDomR`, `hSetB` and
`sfActMass`:
* `h_unit`: the physical field is a real unit vector (Root-F);
* `mu_eq`: the solver mass of the backgrounds and characteristic functions is `μ_j = bgMass`
  (`0` for `j ≤ k₀`, P5 (1.9));
* `muAct_eq`: the mass of the main action of the large-field operators is the physical
  `ν_j L^{-2j}` at every scale (P5 p. 490, Definition II.5.4).
The complex `h`-domains of the localized terms are `hDomR` (for `ℛ^{(k)}_n`; the terms of Def-6
use the landed `XiDom`, outside Def-7) and `hSetB` (boundary terms); the mass of the small-field
action is `sfActMass`. -/
structure FieldClauses (S : Setting) [NeZero S.L] (k0 k : ℕ) (cs : OpConsts) {m₁ N : ℕ} {ϱ : ℝ}
    (sf : SFData S.d S.L m₁ k N ϱ) (hv : EuclideanSpace ℝ (Fin N)) : Prop where
  h_unit : ‖hv‖ = 1
  mu_eq : ∀ j, j ≤ k → cs.mu j = bgMass k0 S.L sf.ν j
  muAct_eq : ∀ j, j ≤ k → cs.muAct j = sf.ν j / (S.L : ℝ) ^ (2 * j)

/-! ### The representation -/

section Rep

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- The number `|𝒩_{k+1} ∩ Z'|_#` of new cubes of a localized history at the step `k → k + 1`
(fine sets of cubes of side `M L^{k+1}`). -/
noncomputable def newCnt (M : ℕ) (a : LocalHistory S n M K) (k : ℕ) : ℕ :=
  (a.P k ∪ a.Q k ∪ a.R k ∪ a.Sset k).ncard / (M * S.L ^ (k + 1)) ^ S.d

/-- The number `|Z^c_k ∩ Z'|_{#k}` of cubes of `𝕋_k` of the component outside `Z_k`. -/
noncomputable def outCnt (M : ℕ) (a : LocalHistory S n M K) (k : ℕ) : ℕ :=
  (a.Z (k + 1) \ a.Z k).ncard / (M * S.L ^ k) ^ S.d

/-- **The step exponent `κ^{(k)}(Z', 𝔞)`** of Definition II.5.11 as a function of the localized
history: `A₃ (log β_k)^{2p₀} |𝒩_{k+1} ∩ Z'|_# - (c₁ log β_k + c₂) |Z^c_k ∩ Z'|_{k+1}`. -/
noncomputable def kappaStepLoc (S : Setting) (P : BudgetConsts) (M : ℕ) :
    ℕ → LocalHistory S n M K → ℝ :=
  fun k a => P.kappaStep S k (newCnt M a k) (outCnt M a k)

/-- **The representation at scale `k` on one torus** (Definition II.6.1), the small-field data
`𝔰` being carried by the family (`RepFam`):
* `hist` — `𝔄`: one history of every class up to scale `k` (completeness is the clause
  `IsComplete` of `IsRep`);
* `SD`, `KD`, `κK` — `𝔇`: the step data (S0)-(S2) with the step exponent `κ^{(k)}`
  (`kappaStepLoc`) and the kept data (S3) whose bound (1.26) has the exponent
  `κK k 𝔞 - C_R λ̂_k^{2d+1} + γ(ϰ)` (`κK` is pinned to `κ^pre_k` by `D4Pin`); indexed by
  localized histories;
* `B` — `ℬ`: the boundary terms `ℬ^{(k)}(X, 𝔸; ψ, ψ', h, g)`, `X ⊂ 𝕋_k` (read at the boundary
  domains `bdryDoms` of `𝔸`). -/
structure Rep (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (R : ℕ → ℝ) (k0 K M : ℕ) [NeZero M]
    [NeZero S.L] (N : ℕ) (geo : Geo S n R M) (cs : OpConsts) (P : BudgetConsts) (k : ℕ) where
  /-- `𝔄` -/
  hist : Finset (LabHist S n R k0 K)
  /-- the exponents `κ_k(Z, 𝔞)` of the kept bound -/
  κK : ℕ → LocalHistory S n M K → ℝ
  /-- the step data -/
  SD : StepData k0 geo cs N (kappaStepLoc (K := K) S P M)
  /-- the kept data -/
  KD : KeptData k0 geo cs N κK S.lam
  /-- the boundary terms -/
  B : LabHist S n R k0 K → Finset (Torus S.d (n k)) → MultiFieldC S n M K N →
    MultiFieldC S n M K N → (Fin N → ℂ) → (GIdx S n M K N → ℂ) → ℂ

variable {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}

namespace Rep

variable (rep : Rep S n R k0 K M N geo cs P k)

/-- The kept exponent `κ''_j(Z, 𝔞, ϰ) = κ_j(Z, 𝔞) - C_R λ̂_j^{2d+1} + γ_j(ϰ)` of a component of
`Z^pre_j(𝔸)` (Definition II.5.7 (S3), Definition II.5.11). -/
noncomputable def keptExp (A : LabHist S n R k0 K) (j : ℕ) (c : A.H.Comp j) : ℝ :=
  rep.κK j (A.H.localHistory M K j c) - S.CR * S.lam j ^ (2 * S.d + 1) +
    rep.KD.gam j (A.lab j c.1)

/-- The label cost `log C_dec(ϰ)` of a component (Definition II.5.11). -/
noncomputable def decor (A : LabHist S n R k0 K) (j : ℕ) (c : A.H.Comp j) : ℝ :=
  Real.log (rep.KD.Cdec (A.lab j c.1))

/-- The exponents `κ_j(Z, 𝔸 ∩ Z)` along the history (Definition II.5.11). -/
noncomputable def kappaH (A : LabHist S n R k0 K) : ∀ j, A.H.Comp j → ℝ :=
  A.H.kappa P (rep.keptExp A)

/-- The pre-`R` exponents `κ^pre_j(Z, 𝔸 ∩ Z) = ∑_Y κ_{j-1}(Y) + κ^{(j-1)}(Z)` (`0` at `j = 0`). -/
noncomputable def kappaPreH (A : LabHist S n R k0 K) : ∀ j, A.H.Comp j → ℝ
  | 0 => fun _ => 0
  | j + 1 => fun Z => A.H.kappaPre P j (rep.kappaH A j) Z

/-- The budget `G_j(Z, 𝔸 ∩ Z) = κ_j - log C_j - H_j |Z|_j` (Definition II.5.11). -/
noncomputable def Gpost (A : LabHist S n R k0 K) : ∀ j, A.H.Comp j → ℝ :=
  A.H.budgetPost P (rep.keptExp A) (rep.decor A)

/-- The pre-`R` budget `G^pre_j(Z, 𝔸 ∩ Z)` (Definition II.5.11). -/
noncomputable def Gpre (A : LabHist S n R k0 K) : ∀ j, A.H.Comp j → ℝ :=
  A.H.budgetPre P (rep.keptExp A) (rep.decor A)

/-- `ℬ^{(k)}(𝔸) = ∑_X ℬ^{(k)}(X, 𝔸)` over the boundary domains of `𝔸` (for the region `Z`,
`Z = Z_k(𝔸)` or `Z^pre_k(𝔸)`). -/
noncomputable def bdrySum (A : LabHist S n R k0 K) (Z : Set (Torus S.d (n k)))
    (ψ ψ' : MultiFieldC S n M K N) (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ) : ℂ :=
  ∑ X ∈ bdryDoms (OmegaCube A.H k) Z, rep.B A X ψ ψ' h g

end Rep

/-! ### (D1) Form -/

/-- The integrand of (D1) for one history: `e^{ℬ^{(k)}(𝔸)} χ_k(Z^c) exp(𝒜_k + ℱ_k + ℛ^{(k)})(Z^c)`
as a function of the internal variables of the family of components (`car`: their fine sets),
with `Z` the region of the history at scale `k`. -/
noncomputable def integrand {ι : Type} [Fintype ι] (a : ι → LocalHistory S n M K)
    (Pk : ∀ i, OpPkg N R (a i) k) (car : ι → Set (Torus S.d (M * n K * S.L ^ K)))
    {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ) (rep : Rep S n R k0 K M N geo cs P k)
    (A : LabHist S n R k0 K) (Z : Set (Torus S.d (n k)))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (x : GCfg a k Pk) : ℂ :=
  Complex.exp (rep.bdrySum A Z
      (MultiField.toC (gMulti a k Pk car (fineSet (S := S) (n := n) M K k (OmegaCube A.H k)) ψk x))
      (MultiField.toC (gFluct a k Pk car x)) (hC hv) g) *
    C.sfFactor Zᶜ ψk hv g

/-- The term `𝕋_k(Z_k(𝔸), 𝔸)[e^{ℬ^{(k)}(𝔸)} χ_k(Z^c_k) exp(𝒜_k + ℱ_k + ℛ^{(k)})(Z^c_k)]` of (D1) for
the post-`R` class, and the absolute convergence of its integral. -/
noncomputable def postTerm {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) : ℂ :=
  gOp (fun c : PostComp A k => A.H.localHistory M K k c.1) k
    (postOp geo cs rep.SD rep.KD A C.hkK) ψk hv g
    (integrand (fun c : PostComp A k => A.H.localHistory M K k c.1)
      (postOp geo cs rep.SD rep.KD A C.hkK)
      (fun c => fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k)))) C rep A
      (A.H.step k).Z ψk hv g)

/-- The integral of the post-`R` term converges absolutely. -/
def PostConv {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) : Prop :=
  GConv (fun c : PostComp A k => A.H.localHistory M K k c.1) k
    (postOp geo cs rep.SD rep.KD A C.hkK) ψk hv g
    (integrand (fun c : PostComp A k => A.H.localHistory M K k c.1)
      (postOp geo cs rep.SD rep.KD A C.hkK)
      (fun c => fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k)))) C rep A
      (A.H.step k).Z ψk hv g)

/-- **(D1) Form** (P5 H1, (1.1), (1.21)): for all real `ψ_k` and all complex `g` with
`‖g‖_{ℓ¹} < 1`, `ρ_k(ψ_k; h, g) = ∑_{𝔸 ∈ 𝔄} 𝕋_k(Z_k(𝔸), 𝔸)[e^{ℬ^{(k)}(𝔸)} χ_k(Z^c_k)
exp(𝒜_k + ℱ_k + ℛ^{(k)})(Z^c_k)]`, with absolutely convergent integrals (`h` the physical
field). -/
def D1Form {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
    (rep : Rep S n R k0 K M N geo cs P k) (hv : EuclideanSpace ℝ (Fin N))
    (ρ : (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) → (GIdx S n M K N → ℂ) → ℂ) : Prop :=
  ∀ (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ),
    g ∈ l1Ball (GIdx S n M K N) →
      (∀ A ∈ rep.hist, PostConv C rep A ψk hv g) ∧
        ρ ψk g = ∑ A ∈ rep.hist, postTerm C rep A ψk hv g

/-! ### (D4) The pinned exponents, (D5) the operator bound, (D6) the budget -/

/-- **(D4)**, the part not carried by the types of `SD` and `KD`: the exponent `κ_j(Z, 𝔞)` of the
kept bound (S3) is the pre-`R` exponent `κ^pre_j(Z, 𝔸 ∩ Z)` of Definition II.5.11, at the kept
components of the histories of `𝔄`, at the scales `1 ≤ j < top` carrying an `R`-record
(`top = k + 1` for `IsRep_k`, `top = k` for `IsRep^pre_k`). -/
def D4Pin (top : ℕ) (rep : Rep S n R k0 K M N geo cs P k) : Prop :=
  ∀ A ∈ rep.hist, ∀ j, 1 ≤ j → j < top → ∀ Z : A.H.Comp j, IsKept A.H j Z → Z.1 ∉ A.H.rem j →
    rep.κK j (A.H.localHistory M K j Z) = rep.kappaPreH A j Z

/-- **(D5) Operator bound at every scale** (P5 (1.26), ARCH R3-07): for every history of `𝔄`,
every `j ≤ k`, every component `Y` of `Z_j(𝔸)` (`j < top`, the scales with an `R`-record) and
every component `Y` of `Z^pre_j(𝔸)`, the localized operator `𝕋_j(Y, 𝔸 ∩ Y)` (resp. `𝕋^pre_j`)
satisfies (1.26) with the exponent `κ_j(Y, 𝔸 ∩ Y)` (resp. `κ^pre_j`). -/
def D5Bound (top : ℕ) (hkK : k ≤ K) (rep : Rep S n R k0 K M N geo cs P k) : Prop :=
  ∀ A ∈ rep.hist, ∀ j (hj : j ≤ k),
    (j < top → ∀ c : A.H.Comp j, c.1 ∉ A.H.rem j →
      PkgBound (A.H.localHistory M K j c) j
        (locOp geo cs rep.SD rep.KD A.adm (fun i c => A.lab i c.1) j (hj.trans hkK) c)
        (rep.kappaH A j c)) ∧
    ∀ c : A.H.Comp j,
      PkgBound (A.H.localHistory M K j c) j (preOpTop geo cs rep.SD rep.KD A j (hj.trans hkK) c)
        (rep.kappaPreH A j c)

/-- **(D6) Budget invariant (H6′)** (`k ≤ k₀`): every component `Z` of `Z_k(𝔸)` satisfies
`t^*(Z) > k` and `G_k(Z, 𝔸 ∩ Z) ≥ τ_{t^*(Z)} + V_k(Z) + ν(Z) + U(Z)`,
`V_k(Z) = 2σ_k ℓ(Γ(Z)) + W_{k+1}(t^*(Z))` (Part I §I.5.3), with the post-`R` bookkeeping. -/
def D6Budget (rep : Rep S n R k0 K M N geo cs P k) : Prop :=
  ∀ A ∈ rep.hist, ∀ c : PostComp A k,
    k < S.tStar (S.postBook k0 k (A.H.bk k c.1)) ∧
      S.tau (S.tStar (S.postBook k0 k (A.H.bk k c.1))) +
          2 * S.sigma k * (S.postBook k0 k (A.H.bk k c.1)).len +
          S.W (k + 1) (S.tStar (S.postBook k0 k (A.H.bk k c.1))) +
          (S.postBook k0 k (A.H.bk k c.1)).nu + S.bank (S.postBook k0 k (A.H.bk k c.1)) ≤
        rep.Gpost A k c.1

/-! ### (D7) Boundary terms -/

/-- Complex block fields at the scales `j ≤ K` (a normed space). -/
abbrev FinFieldC (S : Setting) (n : ℕ → ℕ) (M K N : ℕ) : Type :=
  (j : Fin (K + 1)) → BlockAt S n M K j → Fin N → ℂ

/-- A field at the scales `≤ K`, extended by `0`. -/
def extK (ψ : FinFieldC S n M K N) : MultiFieldC S n M K N :=
  fun j y => if h : j ≤ K then ψ ⟨j, Nat.lt_succ_of_le h⟩ y else 0

/-- The action of `R ∈ O(N)` on a vector of `ℂ^N` (the matrix of `R`). -/
noncomputable def rotC (ρ : OrthN N) (v : Fin N → ℂ) : Fin N → ℂ :=
  fun i => ∑ j, (rotEntry ρ i j : ℂ) * v j

/-- The action of `R ∈ O(N)` on a complex block field. -/
noncomputable def rotM (ρ : OrthN N) (ψ : MultiFieldC S n M K N) : MultiFieldC S n M K N :=
  fun j y => rotC ρ (ψ j y)

/-- The action of a lattice symmetry on a complex block field: `(σψ)(σ y) = ψ(y)`. -/
def symM (σ : LatTorusSym S n M K) (ψ : MultiFieldC S n M K N) : MultiFieldC S n M K N :=
  fun j y => ψ j ((σ.eb j).symm y)

/-- The action of a lattice symmetry on `g`: `(σg)(σ x) = g(x)`. -/
def symG (σ : LatTorusSym S n M K) (g : GIdx S n M K N → ℂ) : GIdx S n M K N → ℂ :=
  fun p => g (σ.ef.symm p.1, p.2)

/-- **(D7) Boundary terms** (P5 H7, (1.38)-(1.39); P5 H5).  For every history `𝔸` of `𝔄` and
boundary domain `X` of `𝔸` at scale `k` (`Z` is `Z_k(𝔸)`, `Zof A`):
* `loc_field`: `ℬ^{(k)}(X, 𝔸)` depends only on `ψ, ψ', g` restricted to `X`;
* `loc_hist`: and on the history only through `𝔸 ∩ X` (the domains `Ω_j ∩ X`, `Ω''_j ∩ X`,
  `Z_j ∩ X`, and the localized histories of the components of `Z_k` meeting `X`);
* `real`: it is real for real arguments;
* `analytic`, `bound`: it is analytic on the H7 domain at `X` (Definition II.3.5 (d), with the
  ideal weights of scale `k`, the masses `μ_j`, the radii `ε_j` of Def-6 and `ε_{1,j}`) and bounded
  there by `B₀ e^{-κ d^cov_k(X mod Ω^c_k)}` (`κ` the decay rate of Def-6), at the external fields
  `hSetB` (open point Q13);
* `rot`: it is jointly `O(N)`-covariant in `(ψ, ψ', h, g)`;
* `euclid`: it is invariant under the lattice symmetries of the torus (`LatTorusSym`, mapping the
  history to the history `RegionIso` with the same kept labels).
`fac` and `rate` are `B₀` and `κ` for `IsRep` (`B_st`, `3κ/2` for `IsRepPre`). -/
structure D7Bdry (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hkK : k ≤ K)
    (rep : Rep S n R k0 K M N geo cs P k) (Zof : LabHist S n R k0 K → Set (Torus S.d (n k)))
    (aw μs ε ε1 νs : ℕ → ℝ) (fac rate : ℝ) (hv : EuclideanSpace ℝ (Fin N)) : Prop where
  loc_field : ∀ A ∈ rep.hist, ∀ X ∈ bdryDoms (OmegaCube A.H k) (Zof A),
    ∀ (ψ₁ ψ₂ ψ'₁ ψ'₂ : MultiFieldC S n M K N) (h : Fin N → ℂ) (g₁ g₂ : GIdx S n M K N → ℂ),
      (∀ j, j ≤ K → ∀ y : BlockAt S n M K j,
        BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) →
          ψ₁ j y = ψ₂ j y ∧ ψ'₁ j y = ψ'₂ j y) →
      (∀ x i, x ∈ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) →
        g₁ (x, i) = g₂ (x, i)) →
      rep.B A X ψ₁ ψ'₁ h g₁ = rep.B A X ψ₂ ψ'₂ h g₂
  loc_hist : ∀ A ∈ rep.hist, ∀ A' ∈ rep.hist, ∀ X : Finset (Torus S.d (n k)),
    X ∈ bdryDoms (OmegaCube A.H k) (Zof A) → X ∈ bdryDoms (OmegaCube A'.H k) (Zof A') →
    (∀ j, j ≤ k →
      fineSet (S := S) (n := n) M K j (OmegaCube A.H j) ∩
          fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) =
        fineSet (S := S) (n := n) M K j (OmegaCube A'.H j) ∩
          fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ∧
      (globalLH A.H M).OmegaDD j ∩ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) =
        (globalLH A'.H M).OmegaDD j ∩
          fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ∧
      (globalLH A.H M).Z j ∩ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) =
        (globalLH A'.H M).Z j ∩ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) →
    (∀ c : PostComp A k, (c.1.1 ∩ X).Nonempty → ∃ c' : PostComp A' k, c'.1.1 = c.1.1 ∧
      A'.H.localHistory M K k c'.1 = A.H.localHistory M K k c.1) →
    (∀ c' : PostComp A' k, (c'.1.1 ∩ X).Nonempty → ∃ c : PostComp A k, c.1.1 = c'.1.1) →
    ∀ ψ ψ' h g, rep.B A X ψ ψ' h g = rep.B A' X ψ ψ' h g
  real : ∀ A ∈ rep.hist, ∀ X ∈ bdryDoms (OmegaCube A.H k) (Zof A),
    ∀ (ψ ψ' : MultiFieldC S n M K N) (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ),
      (∀ j y i, (ψ j y i).im = 0 ∧ (ψ' j y i).im = 0) → (∀ i, (h i).im = 0) →
      (∀ p, (g p).im = 0) → (rep.B A X ψ ψ' h g).im = 0
  analytic : ∀ A ∈ rep.hist, ∀ X ∈ bdryDoms (OmegaCube A.H k) (Zof A), ∀ h ∈ hSetB hv,
    AnalyticOnNhd ℂ
      (fun p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ) =>
        rep.B A X (extK p.1) (extK p.2.1) h p.2.2)
      {p | H7Domain geo.M1 geo.c geo.hM hnn (globalLH A.H M) k hkK
        (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) aw μs ε ε1 νs h
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i))}
  bound : ∀ A ∈ rep.hist, ∀ X ∈ bdryDoms (OmegaCube A.H k) (Zof A), ∀ h ∈ hSetB hv,
    ∀ p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ),
      H7Domain geo.M1 geo.c geo.hM hnn (globalLH A.H M) k hkK
        (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) aw μs ε ε1 νs h
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i)) →
      ‖rep.B A X (extK p.1) (extK p.2.1) h p.2.2‖ <
        fac * Real.exp (-rate * (dCovMod S.L (OmegaCube A.H k) X).toReal)
  rot : ∀ A ∈ rep.hist, ∀ X ∈ bdryDoms (OmegaCube A.H k) (Zof A), ∀ (ρ : OrthN N)
    (ψ ψ' : MultiFieldC S n M K N) (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ),
      rep.B A X (rotM ρ ψ) (rotM ρ ψ') (rotC ρ h) (rotG ρ g) = rep.B A X ψ ψ' h g
  euclid : ∀ A ∈ rep.hist, ∀ A' ∈ rep.hist, ∀ σ : LatTorusSym S n M K, RegionIso σ A.H A'.H →
    (∀ j (c : Finset (Torus S.d (n j))), A'.keptLab j (c.map (σ.ec j).toEmbedding) =
      A.keptLab j c) →
    ∀ X ∈ bdryDoms (OmegaCube A.H k) (Zof A), ∀ (ψ ψ' : MultiFieldC S n M K N)
      (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ),
      rep.B A' (X.map (σ.ec k).toEmbedding) (symM σ ψ) (symM σ ψ') h (symG σ g) =
        rep.B A X ψ ψ' h g

end Rep

/-! ### (D2), (D8), (D9): the small-field data -/

section SF

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **The terms `ℛ^{(k)}_n` satisfy P5 H4** on the Def-6 torus `N₁` (D2, second part): for
`1 ≤ n ≤ m` (`m = m₀ + m₁`) and `X ∈ 𝒟_k`, `ℛ^{(k)}_n(X)` is analytic on
`Ξ^c_k(1, ε_k) × {‖g‖_{ℓ¹} < 1}` (the whole-lattice set `𝔹_k`, the external field in `hDomR`),
local (depends on `(ψ, h, g)|_X`), `O(N)`-invariant and invariant under the symmetries of the
`M`-paving ((1.14)-(1.15)), and bounded there by `fac n · β_k^{-n-1} e^{-κ d_k(X)}` (the bound of
(H.4) with `E₀` replaced by `β_k^{-n-1}`; `fac ≡ 1` for `IsRep`, `fac m = ½` for `IsRepPre`). -/
structure RTermsH4 (P6 : Def6.Consts) (β ν a : ℕ → ℝ) (N₁ : ℕ) [NeZero N₁]
    (Rt : ℕ → Set (Localization.CTorus d L N₁ m₁ k) → Def6.Fld d L N₁ m₁ k N →
      Def6.Fld d L N₁ m₁ k N → Def6.Fld d L N₁ m₁ k N → ℂ) (fac : ℕ → ℝ) : Prop where
  analytic : ∀ nn, 1 ≤ nn → nn ≤ P6.m₀ + m₁ → ∀ X, Def6.IsPolyDom P6.m₀ k X →
    AnalyticOnNhd ℂ
      (fun p : Def6.Fld d L N₁ m₁ k N × Def6.Fld d L N₁ m₁ k N × Def6.Fld d L N₁ m₁ k N =>
        Rt nn X p.1 p.2.1 p.2.2)
      {p | Def6.XiDom (Def6.topGS d L N₁ m₁ k ϱ) (Def6.aIdeal L k (a k))
          (Def6.bgMass L k (β k) (ν k)) k (P6.eps d L k) p.1 p.2.1 ∧
        (∀ x, p.2.1 x ∈ hDomR N) ∧ Def6.l1 p.2.2 < 1}
  loc : ∀ nn X (ψ ψ' h h' g g' : Def6.Fld d L N₁ m₁ k N),
    (∀ z ∈ X, ψ z = ψ' z ∧ h z = h' z ∧ g z = g' z) → Rt nn X ψ h g = Rt nn X ψ' h' g'
  rot : ∀ nn X (R : Matrix (Fin N) (Fin N) ℂ), Def6.IsRot R → ∀ ψ h g,
    Rt nn X (Def6.rotField R ψ) (Def6.rotField R h) (Def6.rotField R g) = Rt nn X ψ h g
  euc : ∀ nn X, ∀ r ∈ Def6.pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L P6.m₀ k,
    ∀ ψ h g, Rt nn (r '' X) (Def6.actField r ψ) (Def6.actField r h) (Def6.actField r g) =
      Rt nn X ψ h g
  bound : ∀ nn, 1 ≤ nn → nn ≤ P6.m₀ + m₁ → ∀ X, Def6.IsPolyDom P6.m₀ k X → ∀ ψ h g,
    Def6.XiDom (Def6.topGS d L N₁ m₁ k ϱ) (Def6.aIdeal L k (a k))
      (Def6.bgMass L k (β k) (ν k)) k (P6.eps d L k) ψ h →
    (∀ x, h x ∈ hDomR N) → Def6.l1 g < 1 →
    ‖Rt nn X ψ h g‖ ≤ fac nn * (β k)⁻¹ ^ (nn + 1) * Real.exp (-P6.κ * Def6.sizeJ P6.m₀ k X)

/-- **(D2) Small-field data** [v1.3: F-1]: `𝔰` satisfies Def-6 at scale `k` (`Def6.IsSFFamily`:
(H.1)-(H.7) in P4's numbering, P5's conventions (1.8)-(1.9), the flow (H.6), and analyticity of
each local `ℰ^{(j)}(y, X)`, `ℳ^{(j)}(x, X)` on `Ξ^c_j(𝔹_j(X); 1, ε_j)` — the accepted ruling
F-1), and the `ℛ^{(k)}_n` satisfy P5 H4 on every Def-6 torus (`RTermsH4`). -/
structure D2SF (P6 : Def6.Consts) (sf : SFData d L m₁ k N ϱ) (fac : ℕ → ℝ) : Prop where
  sfClass : ∃ ρsf : ∀ (N₁ : ℕ) [NeZero N₁], (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) →
      (Fin N → ℝ) → (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ,
    Def6.IsSFFamily P6 sf.β sf.ν sf.a sf.Tm ρsf sf.E
  rTerms : ∀ (N₁ : ℕ) [NeZero N₁], RTermsH4 (ϱ := ϱ) P6 sf.β sf.ν sf.a N₁ (sf.Rt N₁) fac

/-- **(D8) Torus coherence of the small-field data** (roadmap §3.5; P4 (H.4); D-IV.9): the terms
`ℳ^{(j)}(x, X)` and `ℛ^{(k)}_n(X)` of a polymer `X'` of `ℤ^d` that does not wind around two tori
(`NonWind`, Def-6's form of "lies in the image of a box of side `< ℓ/2`") are the same on both,
at the data pulled back from `ℤ^d`.  (For `ℰ^{(j)}(y, X)` this is Def-6's `TorusIndep`, part of
(D2).)  The large-field part of (D8) is not formalized (open point, see the handoff). -/
structure D8SF (m₀ : ℕ) (sf : SFData d L m₁ k N ϱ) : Prop where
  M_eq : ∀ j, 1 ≤ j → j ≤ k → ∀ (x : Fin d → ℤ) (X' : Finset (Fin d → ℤ))
    (ψ h g : Def6.InfFld d N) (N₁ N₂ : ℕ) [NeZero N₁] [NeZero N₂],
    Def6.NonWind L N₁ m₁ k j X' → Def6.NonWind L N₂ m₁ k j X' →
    Def6.IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
      (Def6.Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') →
    Def6.IsPolyDom (L := L) (N₁ := N₂) (m₁ := m₁) (k := k) m₀ j
      (Def6.Ypoly (L := L) (N₁ := N₂) (m₁ := m₁) (k := k) j X') →
    (sf.Tm N₁).M j (fun μ => ((x μ : ℤ) : ZMod _)) (Def6.Ypoly j X') (Def6.pullFld j ψ)
        (Def6.pullFld j h) (Def6.pullFld j g) =
      (sf.Tm N₂).M j (fun μ => ((x μ : ℤ) : ZMod _)) (Def6.Ypoly j X') (Def6.pullFld j ψ)
        (Def6.pullFld j h) (Def6.pullFld j g)
  R_eq : ∀ nn (X' : Finset (Fin d → ℤ)) (ψ h g : Def6.InfFld d N) (N₁ N₂ : ℕ) [NeZero N₁]
    [NeZero N₂],
    Def6.NonWind L N₁ m₁ k k X' → Def6.NonWind L N₂ m₁ k k X' →
    Def6.IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ k
      (Def6.Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) k X') →
    Def6.IsPolyDom (L := L) (N₁ := N₂) (m₁ := m₁) (k := k) m₀ k
      (Def6.Ypoly (L := L) (N₁ := N₂) (m₁ := m₁) (k := k) k X') →
    sf.Rt N₁ nn (Def6.Ypoly k X') (Def6.pullFld k ψ) (Def6.pullFld k h) (Def6.pullFld k g) =
      sf.Rt N₂ nn (Def6.Ypoly k X') (Def6.pullFld k ψ) (Def6.pullFld k h) (Def6.pullFld k g)

/-- **(D9) Coefficients** (P5 (1.42), Theorem 1; v1.2 D-IV.11): `β_k > B L^{k(d-2)}`,
`0 < ν_k ≤ ν̄`, and `k ≤ k₀`. -/
structure D9Coeff (P6 : Def6.Consts) (k0 : ℕ) (sf : SFData d L m₁ k N ϱ) : Prop where
  beta_gt : P6.B * (L : ℝ) ^ (k * (d - 2)) < sf.β k
  nu_pos : 0 < sf.ν k
  nu_le : sf.ν k ≤ P6.νbar
  k_le : k ≤ k0

end SF

/-! ### The family and `IsRep_k` -/

/-- **A family of representations over the admissible tori** (§II.6.2: "a family of
representations … on every admissible torus"): the small-field data `𝔰` (on all Def-6 tori) and,
for every torus `n_K ≥ 1`, the large-field part of the representation. -/
structure RepFam (S : Setting) (R : ℕ → ℝ) (k0 K M : ℕ) [NeZero M] [NeZero S.L] (N : ℕ)
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M) (cs : OpConsts)
    (P : BudgetConsts) (k m₁ : ℕ) (ϱ : ℝ) where
  /-- `𝔰` -/
  sf : SFData S.d S.L m₁ k N ϱ
  /-- `(𝔄, 𝔇, ℬ)` on every torus -/
  lf : ∀ (nK : ℕ) [NeZero nK], Rep S (sides S.L K nK) R k0 K M N (geo nK) cs P k

section IsRep

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}
  {P6 : Def6.Consts} {C7 : Consts7} {k : ℕ} {ϱ : ℝ}

/-- The typing context of the restricted small-field functions on the torus `n_K` (the Def-6 torus
`N₁ = L^{m₀} n_k`). -/
def RepFam.ctx (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ) (hM6 : M = S.L ^ (P6.m₀ + C7.m₁))
    (hkK : k ≤ K) (nK : ℕ) [NeZero nK] : SFCtx S (sides S.L K nK) R M K N k C7.m₁ ϱ where
  geo := geo nK
  hnn := sides_hnn S.L K nK
  hkK := hkK
  cs := cs
  m₀ := P6.m₀
  sf := F.sf
  N₁ := sfIdx S.L P6.m₀ (sides S.L K nK) k
  hT := sfIdx_hT (geo nK) hM6

/-- The ideal weights of scale `k` (the weights of the H7 domain of (D7)). -/
noncomputable def RepFam.weights (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ) : ℕ → ℝ :=
  Def6.aIdeal S.L k (F.sf.a k)

/-- The radii `ε_{1,j}` of the fluctuation fields in the H7 domain (Definition II.1.1). -/
noncomputable def epsOne (S : Setting) (P6 : Def6.Consts) (C7 : Consts7) : ℕ → ℝ :=
  fun j => epsOneRun C7.A0 C7.A1 P6.α₀ (P6.alpha S.d) S.L j

/-- **Definition II.6.2 (Def-7): `IsRep_k(𝖼, rep, ρ)`**, `1 ≤ k`, for a family of representations
`F` and a family of densities `ρ` over the admissible tori (on the torus `n_K`,
`ρ(ψ_k; h, g)` with the physical field `hv`).  Parameters: the constants `𝖼` (`S`, `geo`, `cs`,
`P`, `P6`, `C7`), the initial couplings `β, ν` (for the a priori `k₀`), the horizon `K ≥ k`
(typing), `M = L^{m₀ + m₁}` (typing).  Fields:
* `coh`: the coherence of the constants with `𝔰` and the a priori data;
* `field`: the external-field clauses (open point Q13);
* `complete`: `𝔄` is the set of all histories up to scale `k` (§II.6.1);
* `form` (D1), `sfData` (D2), `pin` (D4, the pinned exponents), `opBound` (D5), `budget` (D6),
  `bdry` (D7), `coherent` (D8, small-field part), `coeff` (D9).
(D3) is built into (D1) and (D4) into the types of `Rep`. -/
structure IsRep (S : Setting) (R : ℕ → ℝ) (k0 K M : ℕ) [NeZero M] [NeZero S.L] (N : ℕ)
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M) (cs : OpConsts)
    (P : BudgetConsts) (P6 : Def6.Consts) (C7 : Consts7) (β ν : ℝ)
    (hv : EuclideanSpace ℝ (Fin N)) (k : ℕ) {ϱ : ℝ} (hM6 : M = S.L ^ (P6.m₀ + C7.m₁))
    (hkK : k ≤ K) (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ)
    (ρ : ∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L K nK) M K k → EuclideanSpace ℝ (Fin N)) →
      (GIdx S (sides S.L K nK) M K N → ℂ) → ℂ) : Prop where
  coh : Coh S R k0 M cs P P6 C7 β ν k F.sf
  field : FieldClauses S k0 k cs F.sf hv
  complete : ∀ (nK : ℕ) [NeZero nK], IsComplete k (k + 1) (F.lf nK).hist
  form : ∀ (nK : ℕ) [NeZero nK], D1Form (F.ctx hM6 hkK nK) (F.lf nK) hv (ρ nK)
  sfData : D2SF P6 F.sf (fun _ => 1)
  pin : ∀ (nK : ℕ) [NeZero nK], D4Pin (k + 1) (F.lf nK)
  opBound : ∀ (nK : ℕ) [NeZero nK], D5Bound (k + 1) hkK (F.lf nK)
  budget : ∀ (nK : ℕ) [NeZero nK], D6Budget (F.lf nK)
  bdry : ∀ (nK : ℕ) [NeZero nK], D7Bdry (sides_hnn S.L K nK) hkK (F.lf nK)
    (fun A => (A.H.step k).Z) F.weights cs.mu (P6.eps S.d S.L) (epsOne S P6 C7) cs.nu C7.B0 P6.κ hv
  coherent : D8SF P6.m₀ F.sf
  coeff : D9Coeff P6 k0 F.sf

/-- **The class `𝓡_k(𝖼)`** (ARCH R3-10): the density families that have a representation. -/
def RepClass (S : Setting) (R : ℕ → ℝ) (k0 K M : ℕ) [NeZero M] [NeZero S.L] (N : ℕ)
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M) (cs : OpConsts)
    (P : BudgetConsts) (P6 : Def6.Consts) (C7 : Consts7) (β ν : ℝ)
    (hv : EuclideanSpace ℝ (Fin N)) (k : ℕ) (ϱ : ℝ) (hM6 : M = S.L ^ (P6.m₀ + C7.m₁))
    (hkK : k ≤ K) :
    Set (∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L K nK) M K k → EuclideanSpace ℝ (Fin N)) →
      (GIdx S (sides S.L K nK) M K N → ℂ) → ℂ) :=
  {ρ | ∃ F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ,
    IsRep S R k0 K M N geo cs P P6 C7 β ν hv k hM6 hkK F ρ}

end IsRep

end Balaban.LargeField.Def7
