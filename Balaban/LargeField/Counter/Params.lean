module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The typing data and the model-free constants of the step counter (Part I, §I.1.2, §I.5.2)

`Setting` bundles the typing constants of §I.1.2 with the abstract sequence `lam = (λ_j)`.
Every derived quantity of the table of §I.1.2 is a definition with no binders:

* radii `r, ρ, crit, ω, D`, window and smallness lengths `nq, n2`, piece cap `νmax`, strip
  length `h`, the blocked scales `blocked E` (= `B(E)`), the core `k1`;
* costs `g, v, w, σ, τ, E`, the sums `W a t = ∑_{j=a}^t w_j`.

`Setting.Ok` collects the typing conditions: the typing data of §I.1.2, the condition (K) of
§I.5.2 and the first part of (H-λ).  The auxiliary functions of §I.5.2 (`critBar`, …) depend on
the typing data only.
-/

@[expose] public section

namespace Balaban.LargeField

/-- The typing constants of §I.1.2 (all real or natural numbers; no hypotheses). -/
structure Typing where
  /-- dimension `d` -/
  d : ℕ
  /-- scale factor `L` -/
  L : ℕ
  /-- cube size `M` -/
  M : ℕ
  /-- the fixed radius coefficient `R_base` -/
  Rb : ℝ
  /-- `θ₊` -/
  θp : ℝ
  /-- `θ₋` -/
  θm : ℝ
  /-- `α` -/
  α : ℝ
  /-- `p₀` -/
  p0 : ℕ
  /-- `p₂` -/
  p2 : ℕ
  /-- `p_R` -/
  pR : ℕ
  /-- `A₂` -/
  A2 : ℝ
  /-- `A₃` -/
  A3 : ℝ
  /-- `A'₃` -/
  A3' : ℝ
  /-- `C_R` -/
  CR : ℝ
  /-- `C_ν` -/
  Cν : ℝ
  /-- `c_v` -/
  cv : ℝ
  /-- `c_H` -/
  cH : ℝ
  /-- `s_*` -/
  sS : ℕ
  /-- `s'` -/
  sP : ℕ
  /-- `c₀` -/
  c0 : ℕ

/-- Typing data together with the abstract sequence `λ = (λ_j)_{j ∈ ℕ}`. -/
structure Setting extends Typing where
  /-- the abstract sequence `λ_j` -/
  lam : ℕ → ℝ

namespace Typing

variable (T : Typing)

/-- `log L` as a real number. -/
noncomputable def logL : ℝ := Real.log T.L

/-- `c_* = 1 + θ₊ / (α log L)`. -/
noncomputable def cStar : ℝ := 1 + T.θp / (T.α * T.logL)

/-- `c' = c_* (1 + 3 θ₊)`. -/
noncomputable def cPrime : ℝ := T.cStar * (1 + 3 * T.θp)

/-- `c'' = c_* + θ₊`. -/
noncomputable def cDPrime : ℝ := T.cStar + T.θp

/-- `C_t = 4 + (1 + 2θ₊)/(α log L)`. -/
noncomputable def Ct : ℝ := 4 + (1 + 2 * T.θp) / (T.α * T.logL)

/-- `C_r = 2 A₂ c'^{p₂} + 1`. -/
noncomputable def Cr : ℝ := 2 * T.A2 * T.cPrime ^ T.p2 + 1

/-- `C_V = 2 · 14^d`. -/
noncomputable def CV : ℝ := 2 * 14 ^ T.d

/-- `C_σ = 2^{d-1} ∑_{n ≥ 1} n^{2d-1} L^{-n}`. -/
noncomputable def Csigma : ℝ :=
  2 ^ (T.d - 1) * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (2 * T.d - 1) * ((T.L : ℝ) ^ (n + 1))⁻¹

/-- `C_w = c_v C_V c₀^d (R_base + 1)^d`. -/
noncomputable def Cw : ℝ := T.cv * T.CV * (T.c0 : ℝ) ^ T.d * (T.Rb + 1) ^ T.d

/-- `C_E` of (F5). -/
noncomputable def CE : ℝ :=
  (1 + 2 ^ (3 * T.d + 1) * T.Csigma) * T.cv * T.CV * Real.sqrt T.d *
    ((T.c0 : ℝ) * (T.Rb + 1)) ^ (T.d - 1) *
    (2 * (T.c0 : ℝ) * (T.Rb + 1) + 2 * T.Rb + T.L + 21)

/-! ### Auxiliary functions of §I.5.2 (real variable `x ≥ 1`) -/

/-- `crit̄(x) = 2 c₀ (R_base x² + 1) + 10`. -/
noncomputable def critBar (x : ℝ) : ℝ := 2 * T.c0 * (T.Rb * x ^ 2 + 1) + 10

/-- `ω̄(x) = 2 R_base x² + L + 11`. -/
noncomputable def omegaBar (x : ℝ) : ℝ := 2 * T.Rb * x ^ 2 + T.L + 11

/-- `D̄(x) = √d (crit̄(x) + ω̄(x))`. -/
noncomputable def Dbar (x : ℝ) : ℝ := Real.sqrt T.d * (T.critBar x + T.omegaBar x)

/-- `ν̄(x) = C_ν x^{p₂} + 1`. -/
noncomputable def nuBar (x : ℝ) : ℝ := T.Cν * x ^ T.p2 + 1

/-- `h̄(x) = log_L (2 √d ν̄(x) M (crit̄(x) + ω̄(x))) + 3`. -/
noncomputable def hBar (x : ℝ) : ℝ :=
  Real.logb T.L (2 * Real.sqrt T.d * T.nuBar x * T.M * (T.critBar x + T.omegaBar x)) + 3

/-- `n̄₂(x) = log_L (L M crit̄(x)) + 1`. -/
noncomputable def n2Bar (x : ℝ) : ℝ := Real.logb T.L (T.L * T.M * T.critBar x) + 1

/-- `Ā(y) = 2 A₂ p₂ θ₊ y^{p₂-1} + C_w y^{2d+1}`. -/
noncomputable def Abar (y : ℝ) : ℝ :=
  2 * T.A2 * T.p2 * T.θp * y ^ (T.p2 - 1) + T.Cw * y ^ (2 * T.d + 1)

/-- `Φ(y) = 2 A₂ (c' y)^{p₂} + C_t C_w c'^{2d+1} y^{2d+2}`. -/
noncomputable def Phi (y : ℝ) : ℝ :=
  2 * T.A2 * (T.cPrime * y) ^ T.p2 + T.Ct * T.Cw * T.cPrime ^ (2 * T.d + 1) * y ^ (2 * T.d + 2)

/-- `Δ̄(x) = 2 + log_L ν̄(x) + log_L (1 + D̄(x)) + n̄₂(2x)`. -/
noncomputable def DeltaBar (x : ℝ) : ℝ :=
  2 + Real.logb T.L (T.nuBar x) + Real.logb T.L (1 + T.Dbar x) + T.n2Bar (2 * x)

/-- `Ḡ(x) = c_* (2 + log_L (ν̄(x) D̄(x)) + log_L (1 + D̄(x))) + 1`. -/
noncomputable def Gbar (x : ℝ) : ℝ :=
  T.cStar * (2 + Real.logb T.L (T.nuBar x * T.Dbar x) + Real.logb T.L (1 + T.Dbar x)) + 1

end Typing

namespace Setting

variable (S : Setting)

/-- The radius unit `r_j = ⌈R_base λ_j²⌉`. -/
noncomputable def r (j : ℕ) : ℕ := ⌈S.Rb * S.lam j ^ 2⌉₊

/-- The spine radius coefficient `ρ_j = c₀ r_j` (the spine radius is `ρ_j + 4`). -/
noncomputable def rho (j : ℕ) : ℕ := S.c0 * S.r j

/-- The critical side `crit_j = 2ρ_j + 10`. -/
noncomputable def crit (j : ℕ) : ℕ := 2 * S.rho j + 10

/-- The component width `ω_j = 2⌊R_base λ_{j-1}²⌋ + L + 11` for `j ≥ 1`, and `ω_0 = L + 11`. -/
noncomputable def omega (j : ℕ) : ℕ :=
  if j = 0 then S.L + 11 else 2 * ⌊S.Rb * S.lam (j - 1) ^ 2⌋₊ + S.L + 11

/-- The connector length `D_j = √d (2ρ_j + 10 + ω_j)`. -/
noncomputable def D (j : ℕ) : ℝ := Real.sqrt S.d * (2 * S.rho j + 10 + S.omega j)

/-- The window length `n_q(j) = min {n ≥ 1 : n log L > λ_j / α} = ⌊λ_j/(α log L)⌋ + 1`. -/
noncomputable def nq (j : ℕ) : ℕ := ⌊S.lam j / (S.α * S.logL)⌋₊ + 1

/-- The smallness length `n_2(j) = min {n ∈ ℕ : L^n > L M crit_j}`. -/
noncomputable def n2 (j : ℕ) : ℕ := sInf {n : ℕ | S.L * S.M * S.crit j < S.L ^ n}

/-- The piece cap `ν_max(j) = ⌈C_ν λ_j^{p₂}⌉`. -/
noncomputable def numax (j : ℕ) : ℕ := ⌈S.Cν * S.lam j ^ S.p2⌉₊

/-- The strip length `h_j = ⌈log_L (2 √d ν_max(j) M (crit_j + ω_j))⌉ + 2`. -/
noncomputable def h (j : ℕ) : ℕ :=
  ⌈Real.logb S.L (2 * Real.sqrt S.d * S.numax j * S.M * (S.crit j + S.omega j))⌉₊ + 2

/-- The blocked core scales `B(E) = ⋃_{ξ ∈ E} [ξ, ξ + h_ξ]`. -/
def blocked (E : Finset ℕ) : Set ℕ := {c | ∃ ξ ∈ E, ξ ≤ c ∧ c ≤ ξ + S.h ξ}

/-- The core of a window ending at `t`: `k₁(t) = max {c ≤ t : c + n_q(c) ≤ t}`, `0` if empty. -/
noncomputable def k1 (t : ℕ) : ℕ := Nat.findGreatest (fun c => c + S.nq c ≤ t) t

/-- The gain per new cube `g_k = ½ A₃ λ_k^{2p₀}`. -/
noncomputable def g (k : ℕ) : ℝ := 1 / 2 * S.A3 * S.lam k ^ (2 * S.p0)

/-- The volume cost coefficient `v_j = c_v C_V λ_j ρ_j^{d-1}`. -/
noncomputable def v (j : ℕ) : ℝ := S.cv * S.CV * S.lam j * (S.rho j : ℝ) ^ (S.d - 1)

/-- The coefficient `w_j = v_j ρ_j`. -/
noncomputable def w (j : ℕ) : ℝ := S.v j * S.rho j

/-- The spine reserve coefficient `σ_k = ∑_{j > k} v_j L^{-(j-k)}`. -/
noncomputable def sigma (k : ℕ) : ℝ := ∑' n : ℕ, S.v (k + 1 + n) * ((S.L : ℝ) ^ (n + 1))⁻¹

/-- The ripeness threshold `τ_t = 2 A₂ λ_t^{p₂}`. -/
noncomputable def tau (t : ℕ) : ℝ := 2 * S.A2 * S.lam t ^ S.p2

/-- The cost of one contact edge `E_k = (1 + 2^{3d+1} C_σ) v_k D_k`. -/
noncomputable def E (k : ℕ) : ℝ := (1 + 2 ^ (3 * S.d + 1) * S.Csigma) * S.v k * S.D k

/-- The partial sums `W_a(t) = ∑_{j=a}^t w_j` (zero if `t < a`). -/
noncomputable def W (a t : ℕ) : ℝ := ∑ j ∈ Finset.Icc a t, S.w j

end Setting

/-- The typing conditions: §I.1.2 (with `d ≥ 3`, as in LF-2) and the condition (K) of §I.5.2. -/
structure Typing.Ok (T : Typing) : Prop where
  three_le_d : 3 ≤ T.d
  two_le_L : 2 ≤ T.L
  one_le_M : 1 ≤ T.M
  two_le_Rb : 2 ≤ T.Rb
  θm_pos : 0 < T.θm
  θm_le_θp : T.θm ≤ T.θp
  α_pos : 0 < T.α
  A2_pos : 0 < T.A2
  A3_pos : 0 < T.A3
  A3'_pos : 0 < T.A3'
  CR_nonneg : 0 ≤ T.CR
  Cν_pos : 0 < T.Cν
  one_le_cv : 1 ≤ T.cv
  cH_nonneg : 0 ≤ T.cH
  /-- (K): `p₂ ≥ 2d + 3`. -/
  p2_ge : 2 * T.d + 3 ≤ T.p2
  /-- (K): `p_R > p₂ + 2d`. -/
  pR_gt : T.p2 + 2 * T.d < T.pR
  /-- (K): `2 p₀ > p₂`. -/
  p0_gt : T.p2 < 2 * T.p0
  /-- (K): `c₀ (1 - L⁻¹) ≥ s_* + 1`. -/
  c0_sS : (T.sS : ℝ) + 1 ≤ T.c0 * (1 - 1 / (T.L : ℝ))
  /-- (K): `c₀ ≥ s' + 1`. -/
  c0_sP : T.sP + 1 ≤ T.c0
  /-- (K): `C_ν ≥ C_r`. -/
  Cr_le : T.Cr ≤ T.Cν

/-- The typing conditions together with (H-λ), first part (`θ₋ ≤ λ_{j+1} - λ_j ≤ θ₊`), and
`λ₀ ≥ max {1, θ₊}`. -/
structure Setting.Ok (S : Setting) : Prop extends Typing.Ok S.toTyping where
  /-- (H-λ), first part: `θ₋ ≤ λ_{j+1} - λ_j ≤ θ₊`. -/
  lam_step : ∀ j, S.θm ≤ S.lam (j + 1) - S.lam j ∧ S.lam (j + 1) - S.lam j ≤ S.θp
  one_le_lam0 : 1 ≤ S.lam 0
  θp_le_lam0 : S.θp ≤ S.lam 0

end Balaban.LargeField
