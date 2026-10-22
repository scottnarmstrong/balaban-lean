# RENORM-RELEVANT: interface proposal for the relevant parts of the new level

Proposal (C3, not yet Lean). Goal: discharge `hpsi`, `hh`, `hmom` of `Def6.renormCondAlong_of_system`
(`SmallField/RenormCondStep.lean`) for Φ's normalized new level, generic in the level `k`.

## 1. Inputs from Φ (names to be confirmed by W1146u)
* `Tm'` the level-`(k+1)` terms of `sf'.Tm`: `E (k+1) y Y = 1_{y∈Y} AE y Y`, `AE` the paving-group average of the
  shifted labels `f' = f − f(p₀)` (`localClass_newLevel_of_expansion_cast`, `NewLevelTies.newLevel_localFamilies_composed_gap`);
  `E_{k+1} = SFData.E` carries the constant (`hval` then holds for `Tm'`).
* The density as a function of the counterterm parameter: `𝒟'_ξ : data → ℂ`, `𝒟'_ξ = densE0_ξ − densE0_ξ(p₀)` with
  `densE0_ξ = E0θ_ξ + oldE_ξ + (C₁ − C₂)_ξ` (`RenormExpInput`: `E0θ`, `oldE`; `renC1On`, `renC2On`; Lemma 3.5
  `renormC1`, `renormC2`). Needed as a hypothesis-free definition: `𝒟E_ξ := E0θ_ξ + oldE_ξ` and `𝒟C_ξ := (C₁ − C₂)_ξ`,
  summed over the blocks of the cover (`blk`, `Ys`, `renYs`), each shifted by its value at `p₀`.
* The identification (Φ's construction, supplied): `Tm'` is the localized expansion of `𝒟'_{ξ⁰}` at the chosen solution `ξ⁰`
  (`IsLocExp … (E0θ z + oldE z)`, `thm31g_Eu_of_input`, `thm31g_C1/C2_of_input` give the expansions for every `ξ` in the polydisc).

## 2. The four functionals and the shape
Let `rel_i` (i = val, dpsi, dh, mom) be the four functionals of `RenormCondAlong` on a density family:
`val`: value at the unit constant configuration `p₀`; `dpsi`: `d/dt` along `(1+t)e`; `dh`: `∂_h [e]`; `mom`: `Σ_x |x|² ∂²/∂ψ(x)∂ψ(0)`.
Write `rel(𝒟) : Fin 3 → ℂ` for `(dpsi, dh, mom)`. Statement (generic in `k`, `m₀`, with `Λ = (βε, β, β)`):
```
theorem renormRelevant {…} (A := matrixInfty a v τ c₁ c₂ ε)
  (ξ : Fin 3 → ℂ) (hξ : ‖ξ‖ < r₀)
  (c f : Fin 3 → ℂ → …)        -- defined below, not hypotheses
  : relParts (Tm'_ξ) = fun i => Λ i * (A.mulVec ξ + c ξ - f ξ) i
```
where `relParts T := (deriv … ElocInf …, fderiv … , lim momentSum …)` are exactly the right sides of `hpsi/hh/hmom`.

## 3. Definition of `c`, `f` (the ones fed to `rg_step_infty`/`baseRg_step`)
* `f_i(ξ) := −Λ_i⁻¹ · rel_i(𝒟E_ξ)` (the ℰ'' and old-term side; bounded by `η` on the polydisc by `thm31g_Eu_of_input`, Cauchy).
* `c_i(ξ) := Λ_i⁻¹ · rel_i(𝒟C_ξ) − (A ξ)_i` (the counterterm side minus its linear part).
Then the identity of §2 is *definitional* once `rel_i` is additive on the sum `𝒟E + 𝒟C` (S1 below). The analytic content
is that `c` is second order, i.e. `hcb : ‖c(ξ)‖ ≤ κ ε'²`.

## 4. What is proved generically, what is supplied
(S1) additivity and shift invariance of `rel_i` for stabilizing families (`ElocInf`, `momentSum`; derivatives kill the
constant, `val` of the shifted family is `0` at `p₀`): generic, ~300 lines.
(S2) Schwarz-type bound: `c` analytic on the closed polydisc of radius `c₁₀`, `‖c‖ ≤ M`, `c(0) = 0`, `Dc(0) = 0` ⇒
`‖c(ξ)‖ ≤ (M/c₁₀²)‖ξ‖²`: generic, ~120 lines (gives `hcb` with `κ = M/c₁₀²`).
(S3) `c(0) = 0` and `Dc(0) = 0`, i.e. `∂_ξ rel(𝒟C_ξ)|₀ = Λ·A`: the computation of P4 (5.10)–(5.14) /
`SMALLFIELD.md` §3.3 from the explicit `renormC1` (linear in `ξ₃, ζ, νξ₂`, `ζ²` term) and `C₂ = O(ξ²)` (`δφ = O(ξ)`,
`lemma35_ii_bound`); entries of `matrixInfty` at `(a_{k+1}, v = ν_{k+1}, τ, c₁(v), c₂(v), ε)`. Supplied by this task, not by Φ;
the lattice sums `c₁, c₂, τ` enter as the parameters of `matrixInfty` (hypotheses = their definitions as sums), ~900 lines.
(S4) analyticity of `ξ ↦ rel(𝒟C_ξ)` and the bound `M` from `thm31g_C1/C2_of_input`: instance of landed statements, ~200.
Supplied by Φ: the identification of `Tm'` with the expansion of `𝒟'_{ξ⁰}` (§1) and `TorusIndep` for `hmom`.

## 5. Open points for W1146u
1. Is `Tm'` built from `𝒟'_{ξ⁰}` for the same `ξ⁰` that solves the system (so `hsys` and the identity use one `ξ`)?
2. The cover index `z` of `RenormExpInput` and the sum over blocks: the statement above sums all blocks; confirm that `AE`
   (the paving-group average) leaves `rel_i` unchanged (it should: `rel_i` is a sum over the whole torus).
3. Which `a, v` enter the matrix: `a_{k+1}` and `ν_{k+1}` of the renormalized flow depend on `ξ`; P4 puts the `ξ`-dependence
   of `A` into `c̃` (`c̃ = c + (A(ξ) − A(0))ξ`). The proposal uses `A(0)`; `c` then includes `(A(ξ) − A(0))ξ`.

## 6. S3 plan and a finding on the `dh` row (C3, orchC-rel3)

The four functionals are evaluated on `𝒟C_ξ = C₁ − C₂` at the constant configurations `(ψ, h) = ((1+t)e, e)` and
`(e, (1+s)e)`. For these data the background is explicit and constant (no Green function): `φ = e`,
multiplier `α = a t` (resp. `ν s`), and the renormalized datum `((1+ζ)ψ, h)` has the constant background `e` too, so
`δφ = 0` and `C₂ ≡ 0` along both curves. Statements to prove (with `deriv`/`fderiv`, the right sides of `hpsi`/`hh`):
(S3a) `deriv (t ↦ 𝒟C_ξ(0; (1+t)e, e)) 0 = a (1+ξ₃)(ζ + ζ²)` (per block weight), i.e. row 1 of `A` plus second-order terms,
using `renormC1` at `φ = e`: the block term `ξ₃/2 · a t²` has derivative `0`, the cross term `(1+ξ₃) ζ a ⟨Ψ, Ψ−Qφ⟩`
with `⟨Ψ,Ψ−Qφ⟩ = (1+t)t` gives `(1+ξ₃) ζ a`, and `(1+ξ₃) ζ²/2 · a (1+t)²` gives `(1+ξ₃) ζ² a`.
(S3b) `fderiv (h ↦ 𝒟C_ξ(0; e, h)) e e`. **Finding:** with the landed convention `action ∋ (ν/2)‖φ − h‖²`
(and `renormC1 ∋ (νξ₂/2) massPair`) this derivative is `0` for all `ξ`: `massPair = s²` along `h = (1+s)e`. So
row 2 of `A` (`a₂₂ = 1`, the term `βξ₂` of (E2)) is NOT produced by `𝒟C`. In P4's convention the mass term is
`ν(1 − φ·h)` (no `‖h‖²` term), whose radial `h`-derivative is `−νφ·e ≠ 0`; the two conventions differ by
`(ν/2)(‖h‖² − 1)` per site, so `rel_dh` differs by `ν` per site, and `ν_{k+1} = ν_k L²(1+ξ₃)/(1+ξ₂)` makes that
difference depend on `ξ₂` nonlinearly (`−β_uν_u ξ₂` at first order). Decision needed (main orchestrator / CLASS-RULINGS Q-B):
either `dh` of the class is the derivative of `ℰ` with the `ν‖h‖²/2` bookkeeping of P4 (then `A` row 2 and `Λ₂` change by
the factor `ν`), or the system's second equation is stated for the Lean `dh`. Until decided, S3b is not coded.
(S3c) the second moment: `Σ_x |x|² ∂²/∂ψ(x)∂ψ(0)`: needs the first-order response of the background to a local
perturbation (`φ^{(1)} = aGQ*ψ'_⊥`, `G` the lattice Green function) — the genuinely non-elementary part (P4 (5.8)–(5.14)).
### Answers of W1146u (agreed; recorded 2026-10-22)
1. **One `ξ⁰`.** The step map `Φ` fixes one `ξ⁰` (working name `stepXi κ c₉ β ν k sf`), the solution of
   `hsys` for the triple `(A(0), c, f)` of the task Q23. The same `ξ⁰` is used in the flow
   (`β_{k+1}`, `ν_{k+1}`, `z_{k+1}`) and in the new level built from `𝒟'_{ξ⁰}`, so `hsys` and the identity of
   `renormRelevant` use one `ξ`.
2. **The paving average does not change `rel_i`.** The torus functionals pass through the exact identity
   `Edens_{k+1} = Σ_z 𝒟(z)` (`LocalClassDensityLevelCast.lean`, lines 293–300). The per-site functionals
   `val`, `dpsi`, `dh` at `y = 0` pass through the per-centre identity `Eloc_{k+1}(y) = 𝒟(y)`
   (`localClass_centre_Eloc_eq_chart`, `LocalClassDensityCentre.lean:55`); W1146u exports it as an extra
   conclusion (item (5a)) of `localClass_newLevel_of_expansion_hat`.
3. **`A = matrixInfty` at `ξ = 0`.** The matrix is evaluated at `a_{k+1}(0)`, `ν_{k+1}(0)`; the difference
   `(A(ξ) − A(0)) ξ` is part of `c`, which is then second order as before.

Objects of `Φ` to write against: `f` from `newLevel_localFamilies_composed_gap` (sets
`{x' | torusCast x' ∈ hatSet m₀ (k+1) Y}` on `(N₁', m₁ + hatScale)`); the unit constant configuration
`p₀ = (constFld (Pi.single 0 1), constFld (Pi.single 0 1))`; `f' = f − f(p₀)`; the labels `Tl` as in
`newLevelClausesAt_of_localFamilies` (`Spine/NewLevelAssembly.lean`); `AE'` in the `hAE` form
(`LocalClassDensityLevelCast.lean:133–145`); `𝒟' y q = Jr.densE0 C y q − Jr.densE0 C y p₀`
(`LocalClassDensityHAnalytic.lean:320`); the new level `E (k+1) y Y = 1_{y∈Y} · AE' y Y`,
`gs (k+1) = hatGSOf m₀ (k+1)`; the constant `densE0 z p₀ · |T^{(k+1)}_1|` goes into `E_{k+1}` through `ΦE`.
