module

public import Balaban.LargeField.Budget.Counts
public import Balaban.LargeField.Analytic.Constants
public import Balaban.LargeField.Counter.Params
public import Balaban.LargeField.History.FlowBook

/-!
# Exponents, combinatoric factors and the budget (Part II, Definition II.5.11)

The running constants entering the budget are bundled in `BudgetConsts`: `c₁, c₂, H₀` and the
sequence `β_j`.  For the step `k → k+1` and a component `Z'` of `Z^pre_{k+1}`:

* `kappaStep`: `κ^{(k)} = A₃ (log β_k)^{2p₀} |𝒩_{k+1} ∩ Z'|_# - (c₁ log β_k + c₂) |Z^c_k ∩ Z'|_{k+1}`;
* `kappaPre`: `κ^pre_{k+1}(Z') = ∑_{Y ∈ Anc_k(Z')} κ_k(Y) + κ^{(k)}`;
* `logCPre`: `log C^pre_{k+1}(Z') = ∑_Y log C_k(Y) + |Z_k ∩ Z'|_{#k} + (5/4) |Z^c_k ∩ Z'|_{#k}`;
* `budgetG`: `G = κ - log C - H_k |Z|_k`;
* `kappa`, `logC`: the post-`R` functions along the history, recursively: the pre value, except
  for the kept ripe components (`1 ≤ k ≤ k₀`, ripe), where the kept data (S3) replaces `κ` and
  the label cost `log C_dec(ϰ)` is added to `log C`.

The volume of `c` cubes of `π_k` is `M^d c` (`cubeVol`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

/-- The running constants of the budget: `c₁, c₂, H₀` and the sequence `β_j` (so
`H_j = H₀ log β_j`). -/
structure BudgetConsts where
  c1 : ℝ
  c2 : ℝ
  H0 : ℝ
  beta : ℕ → ℝ

namespace BudgetConsts

variable (S : Setting) (P : BudgetConsts)

/-- The volume (number of sites of `𝕋_k`) of `c` cubes of `π_k`: `M^d c`. -/
noncomputable def cubeVol (c : ℕ) : ℝ := (S.M : ℝ) ^ S.d * c

/-- `κ^{(k)}`: `A₃ (log β_k)^{2p₀} |𝒩_{k+1} ∩ Z'|_# - (c₁ log β_k + c₂) |Z^c_k ∩ Z'|_{k+1}`, where
`nNew = |𝒩_{k+1} ∩ Z'|_#` and `nOut = |Z^c_k ∩ Z'|_{#k}` (so `|Z^c_k ∩ Z'|_{k+1} = L^{-d} M^d nOut`). -/
noncomputable def kappaStep (k nNew nOut : ℕ) : ℝ :=
  S.A3 * Real.log (P.beta k) ^ (2 * S.p0) * nNew -
    (P.c1 * Real.log (P.beta k) + P.c2) * ((S.M : ℝ) ^ S.d / (S.L : ℝ) ^ S.d * nOut)

/-- `G = κ - log C - H_k |Z|_k` for a component of `c` cubes at scale `k`. -/
noncomputable def budgetG (k : ℕ) (kap lc : ℝ) (c : ℕ) : ℝ :=
  kap - lc - HRun P.H0 P.beta k * cubeVol S c

end BudgetConsts

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  (H : RegionHistory S n R k0) (P : BudgetConsts)

/-- `κ^pre_{k+1}(Z', 𝔞) = ∑_Y κ_k(Y) + κ^{(k)}(Z')` given the post-`R` exponents `κ_k` of the
old parts. -/
noncomputable def kappaPre (k : ℕ) (κ : H.Comp k → ℝ) (Z' : H.Comp (k + 1)) : ℝ :=
  ∑ c ∈ H.parts k Z', κ c +
    P.kappaStep S k (Z'.1 ∩ H.newCubes (k + 1)).card (H.outCubes k Z').card

/-- `log C^pre_{k+1}(Z', 𝔞) = ∑_Y log C_k(Y) + |Z_k ∩ Z'|_{#k} + (5/4) |Z^c_k ∩ Z'|_{#k}`. -/
noncomputable def logCPre (k : ℕ) (logC : H.Comp k → ℝ) (Z' : H.Comp (k + 1)) : ℝ :=
  ∑ c ∈ H.parts k Z', logC c + (H.oldCubes k Z').card + 5 / 4 * (H.outCubes k Z').card

/-- `G^pre_k(Z)`: `0` at `k = 0` (no components); `κ^pre - log C^pre - H_{k+1} |Z'|_{k+1}`
for `Z'` at scale `k+1`, from the post-`R` exponents and factors of the previous scale. -/
noncomputable def Gpre (κ logC : ∀ k, H.Comp k → ℝ) : ∀ k, H.Comp k → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun Z' =>
      P.budgetG S (k + 1) (H.kappaPre P k (κ k) Z') (H.logCPre k (logC k) Z') Z'.1.card

/-- `G_k(Z) = κ_k(Z) - log C_k(Z) - H_k |Z|_k` from given `κ_k`, `log C_k`. -/
noncomputable def Gpost (κ logC : ∀ k, H.Comp k → ℝ) (k : ℕ) (c : H.Comp k) : ℝ :=
  P.budgetG S k (κ k c) (logC k c) c.1.card

/-- The condition under which the kept data (S3) enters: the component is ripe at a scale
`1 ≤ k ≤ k₀`. -/
def IsKeptEvent (k : ℕ) (c : H.Comp k) : Prop :=
  1 ≤ k ∧ k ≤ k0 ∧ S.Ripe k (H.bk k c)

open Classical in
/-- `κ_k(Z, 𝔞)` (Definition II.5.11): the pre-`R` recursion `κ_{k+1} = ∑ κ_k + κ^{(k)}`, with the
kept data `κK` (S3) for the kept ripe components. -/
noncomputable def kappa (κK : ∀ k, H.Comp k → ℝ) : ∀ k, H.Comp k → ℝ
  | 0, _ => 0
  | k + 1, Z' =>
      if H.IsKeptEvent (k + 1) Z' then κK (k + 1) Z' else H.kappaPre P k (fun c => kappa κK k c) Z'

open Classical in
/-- `log C_k(Z, 𝔞)` (Definition II.5.11): `log C_{k+1} = ∑ log C_k + |Z_k ∩ Z'|_{#k} +
(5/4)|Z^c_k ∩ Z'|_{#k}`, plus the decoration `δ` (`log C_dec(ϰ)`, the kept label (S3)) for the
kept ripe components: `log C_k(Z, 𝔞'') = log C_k(Z, 𝔞) + log C_dec(ϰ)`. -/
noncomputable def logC (δ : ∀ k, H.Comp k → ℝ) : ∀ k, H.Comp k → ℝ
  | 0, _ => 0
  | k + 1, Z' =>
      H.logCPre k (fun c => logC δ k c) Z' + if H.IsKeptEvent (k + 1) Z' then δ (k + 1) Z' else 0

/-- The budget `G_k` along the history (Definition II.5.11). -/
noncomputable def budgetPost (κK δ : ∀ k, H.Comp k → ℝ) (k : ℕ) (c : H.Comp k) : ℝ :=
  H.Gpost P (H.kappa P κK) (H.logC δ) k c

/-- The pre-`R` budget `G^pre_k` along the history (Definition II.5.11). -/
noncomputable def budgetPre (κK δ : ∀ k, H.Comp k → ℝ) : ∀ k, H.Comp k → ℝ :=
  H.Gpre P (H.kappa P κK) (H.logC δ)

end RegionHistory

end Balaban.LargeField
