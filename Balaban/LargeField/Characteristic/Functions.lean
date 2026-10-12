module

public import Balaban.LargeField.Characteristic.Reg
import Mathlib.Tactic.Linarith

/-!
# The characteristic functions (Part II, Definitions II.3.1-II.3.2)

All characteristic functions are indicator functions (`charFn`) of conditions on *real*
configurations of the integration variables (never continued analytically, Part III audit
P3-02/P3-03). A configuration of block variables is a `BlockCfg`: a real vector `ψ_j(y) ∈ ℝ^N`
for each `j`-block `y` of the level-`k` fine torus (`ψ_k` on the `k`-blocks is
`BlockCfg d N₀ L k k N`, `θ` on the `(k+1)`-blocks at level `k+1` is `BlockCfg d N₀ L (k+1) (k+1) N`).
Cubes `□ ∈ π_q` are the points `y0` of the cube torus `Torus d n` (side `L ^ q * (c * M1)` in fine
units, as in `genCube`), `□^{∼r}` is `cubeNbhd` (the fine set of the `r`-neighbourhood) and
`T_k(X)`, `S(X)` are the fine set of `X`.

* `chiK` (item 1, P5 (1.18)-(1.19)), `chiNext` (item 5, P6 (2.1) = P5 (1.19) at `k + 1`);
* `chiPrimeOld` (item 2, P5 (2.5)), `chiPrimeNew` (item 3, P5 (2.13)), `chiFluct` (item 4,
  P5 (2.42));
* `cubeProd`, `cubeProdCompl`: `χ(X) = ∏_{□ ⊂ X} χ(□)` and `χ^c(X) = ∏ (1 - χ(□))` (P5 (2.6)).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

set_option linter.unusedSectionVars false

/-- A real configuration of the variables `ψ_j(y) ∈ ℝ^N` on the `j`-blocks of the level-`k`
fine torus `𝕋 = Torus d (N₀ * L ^ k)`. -/
abbrev BlockCfg (d N₀ L k j N : ℕ) : Type :=
  Torus d (N₀ * L ^ (k - j)) → Fin N → ℝ

/-- The complexification of a real configuration. -/
def BlockCfg.toC {d N₀ L k j N : ℕ} (ψ : BlockCfg d N₀ L k j N) :
    Torus d (N₀ * L ^ (k - j)) → Fin N → ℂ := fun y i => (ψ y i : ℂ)

/-- The indicator function of a condition. -/
noncomputable def charFn {X : Type*} (P : X → Prop) : X → ℝ :=
  Set.indicator {x | P x} (fun _ => (1 : ℝ))

theorem charFn_apply {X : Type*} (P : X → Prop) (x : X) :
    charFn P x = by classical exact if P x then 1 else 0 := by
  classical
  unfold charFn
  by_cases h : P x <;> simp [h]

theorem charFn_eq_one {X : Type*} {P : X → Prop} {x : X} (h : P x) : charFn P x = 1 := by
  unfold charFn; simp [h]

theorem charFn_eq_zero {X : Type*} {P : X → Prop} {x : X} (h : ¬ P x) : charFn P x = 0 := by
  unfold charFn; simp [h]

/-- Products over a set of cubes: `χ(X) = ∏_{□ ∈ X} χ(□)`. -/
def cubeProd {d n : ℕ} {X : Type*} (χ : Torus d n → X → ℝ) (A : Finset (Torus d n)) (x : X) : ℝ :=
  ∏ y ∈ A, χ y x

/-- `χ^c(X) = ∏_{□ ∈ X} (1 - χ(□))` (P5 (2.6)). -/
def cubeProdCompl {d n : ℕ} {X : Type*} (χ : Torus d n → X → ℝ) (A : Finset (Torus d n))
    (x : X) : ℝ :=
  ∏ y ∈ A, (1 - χ y x)

section Chi

variable {d M1 N₁ L N : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

variable (M1 N₁ L) in
/-- The fine set of the `r`-neighbourhood `□^{∼r}` of the `π_q`-cube `y0` of the cube torus
`Torus d n`, `T_q(□^{∼r})` and `S(□^{∼r})` of the source. -/
noncomputable def cubeNbhd (q c n r : ℕ) (y0 : Torus d n) :
    Finset (Torus d (M1 * N₁ * L ^ q)) :=
  cubePre M1 N₁ L q (L ^ q * (c * M1)) n (nbhd r {y0})

section Single

variable {q : ℕ} (a : ℕ → ℝ) (μ δ : ℝ) (h : Fin N → ℝ) (c n : ℕ)

/-- The lifted data `lift_q ψ_q` of the cube `□` on `G_q(□)`. -/
noncomputable def cubeData (y0 : Torus d n) (ψ : BlockCfg d (M1 * N₁) L q q N) :
    BgData (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) N :=
  liftSingle (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) ψ.toC
    (fun i => (h i : ℂ))

/-- **Definition II.3.2 item 1** (P5 (1.18)-(1.19)): the condition `χ_q(□) = 1`,
`Reg_q(G_q(□), lift_q ψ_q, δ; T_q(□^∼), S(□^∼))`. -/
def ChiKProp (y0 : Torus d n) (ψ : BlockCfg d (M1 * N₁) L q q N) : Prop :=
  Reg (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) a μ
    (cubeData h c n y0 ψ) δ (cubeNbhd M1 N₁ L q c n 1 y0) (cubeNbhd M1 N₁ L q c n 1 y0)

/-- `χ_q(□)`: the characteristic function of the cube `□ = y0` (mass `μ = μ_q`, weights `a`,
tolerance `δ = δ_q`, the `h`-conditions being present only for `μ > 0`). -/
noncomputable def chiK (y0 : Torus d n) : BlockCfg d (M1 * N₁) L q q N → ℝ :=
  charFn (ChiKProp a μ δ h c n y0)

/-- **Definition II.3.2 item 5** (P6 (2.1) = P5 (1.19) at `k + 1`): `χ_{k+1}(□')` for the cube
`□' ∈ π_{k+1}` and `ψ_{k+1}`; this is `chiK` at the level `k + 1`
(`𝔹_{k+1}(□'^{∼2}) = G_{k+1}(□')`). -/
noncomputable def chiNext (k : ℕ) (y0 : Torus d n) :
    BlockCfg d (M1 * N₁) L (k + 1) (k + 1) N → ℝ :=
  chiK a μ δ h c n y0

theorem chiNext_eq (k : ℕ) (y0 : Torus d n) :
    chiNext (M1 := M1) (N₁ := N₁) (L := L) (N := N) a μ δ h c n k y0 =
      chiK (q := k + 1) a μ δ h c n y0 := rfl

end Single

section Mixed

variable {k : ℕ} (a : ℕ → ℝ) (μ δ νk : ℝ) (h : Fin N → ℝ) {c n : ℕ}
  (hm : N₁ * L ^ (k + 1 - (k + 1)) = c * n) (y0 : Torus d n)
  (Om : Finset (Torus d (M1 * N₁ * L ^ (k + 1)))) (hOm : IsBlockUnion L (M1 * N₁) (k + 1) (k + 1) Om)

/-- The mixed lifted data `lift_{k,k+1}(ψ_k, θ)` on `G_{k+1}(□')`, `Ω = Ω_{k+1} = Om`. -/
noncomputable def mixedData (ψ : BlockCfg d (M1 * N₁) L (k + 1) k N)
    (θ : BlockCfg d (M1 * N₁) L (k + 1) (k + 1) N) :
    BgData (genCubeMixed hm y0 Om hOm) N :=
  liftMixed (genCubeMixed hm y0 Om hOm) hOm (genCubeMixed_top_subset hm y0 Om hOm) ψ.toC θ.toC
    (fun i => (h i : ℂ))

/-- **Definition II.3.2 item 3** (P5 (2.13)): the condition `χ'_{k+1}(□') = 1` for the pair
`(ψ_k, θ)`: `D = lift_{k,k+1}(ψ_k, θ) ∈ 𝒟_ℝ(G_{k+1}(□'))` and the inequalities of
`RegMixedIneq` with `ℓ = ℓ_k = L ^ k`, `T_k(□'^∼ ∖ Ω_{k+1})`, `T_{k+1}(□'^∼ ∩ Ω_{k+1})`,
`S(□'^∼)`; `νk` is the dimensionless mass `ν_k` of the `h`-conditions. -/
def ChiPrimeNewProp (ψ : BlockCfg d (M1 * N₁) L (k + 1) k N)
    (θ : BlockCfg d (M1 * N₁) L (k + 1) (k + 1) N) : Prop :=
  InUnionDomainR (genCubeMixed hm y0 Om hOm) (bgC1 d L N) μ (mixedData h hm y0 Om hOm ψ θ) ∧
  RegMixedIneq (genCubeMixed hm y0 Om hOm) a μ (mixedData h hm y0 Om hOm ψ θ)
    ((L : ℝ) ^ k) νk δ (cubeNbhd M1 N₁ L (k + 1) c n 1 y0 \ Om)
    (cubeNbhd M1 N₁ L (k + 1) c n 1 y0 ∩ Om) (cubeNbhd M1 N₁ L (k + 1) c n 1 y0)

/-- `χ'_{k+1}(□')` (P5 (2.13)). -/
noncomputable def chiPrimeNew :
    BlockCfg d (M1 * N₁) L (k + 1) k N × BlockCfg d (M1 * N₁) L (k + 1) (k + 1) N → ℝ :=
  charFn fun p => ChiPrimeNewProp a μ δ νk h hm y0 Om hOm p.1 p.2

end Mixed

section Old

variable {k : ℕ} (δ : ℝ) (c n : ℕ) (y0 : Torus d n)

open Classical in
/-- `(Q ψ_k)(y) = L^{-d} ∑_{y' ∈ T_k(B_{k+1}(y))} ψ_k(y')`, the sum over the `k`-blocks inside
the `(k+1)`-block of the site `x`. -/
noncomputable def blockSumQ (ψ : BlockCfg d (M1 * N₁) L (k + 1) k N)
    (x : Torus d (M1 * N₁ * L ^ (k + 1))) : Fin N → ℝ := fun i =>
  ((L : ℝ) ^ d)⁻¹ * ∑ y' ∈ (Finset.univ.filter fun y' : Torus d (M1 * N₁ * L ^ (k + 1 - k)) =>
      ∃ x', jBlock d L (M1 * N₁) (k + 1) k x' = y' ∧
        jBlock d L (M1 * N₁) (k + 1) (k + 1) x' = jBlock d L (M1 * N₁) (k + 1) (k + 1) x),
    ψ y' i

/-- **Definition II.3.2 item 2** (P5 (2.5)): `|θ(y) - (Q ψ_k)(y)| < 2 δ` for the
`(k+1)`-blocks `y` of the cube `□'`. -/
def ChiPrimeOldProp (ψ : BlockCfg d (M1 * N₁) L (k + 1) k N)
    (θ : BlockCfg d (M1 * N₁) L (k + 1) (k + 1) N) : Prop :=
  ∀ x ∈ cubeNbhd M1 N₁ L (k + 1) c n 0 y0,
    rn (fun i => θ (jBlock d L (M1 * N₁) (k + 1) (k + 1) x) i - blockSumQ ψ x i) < 2 * δ

/-- `χ'^{(k)}(□')` (P5 (2.5)). -/
noncomputable def chiPrimeOld :
    BlockCfg d (M1 * N₁) L (k + 1) k N × BlockCfg d (M1 * N₁) L (k + 1) (k + 1) N → ℝ :=
  charFn fun p => ChiPrimeOldProp (M1 := M1) (N₁ := N₁) (L := L) δ c n y0 p.1 p.2

/-- **Definition II.3.2 item 4** (P5 (2.42)): `|ψ'_k(x)| < p_1(β_k)` on the `k`-blocks of `□'`;
`p1` stands for `p_1(β_k)`. -/
def ChiFluctProp (p1 : ℝ) (ψ' : BlockCfg d (M1 * N₁) L (k + 1) k N) : Prop :=
  ∀ x ∈ cubeNbhd M1 N₁ L (k + 1) c n 0 y0, rn (ψ' (jBlock d L (M1 * N₁) (k + 1) k x)) < p1

/-- `χ^{(k)}(□')` (P5 (2.42)). -/
noncomputable def chiFluct (p1 : ℝ) : BlockCfg d (M1 * N₁) L (k + 1) k N → ℝ :=
  charFn (ChiFluctProp (M1 := M1) (N₁ := N₁) (L := L) c n y0 p1)

end Old

end Chi

end Balaban.LargeField
