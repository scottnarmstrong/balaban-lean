# RENORM-BRIDGE: (H.5) of the new level from a solution of the counterterm system

Design note (C3). Lean: `Balaban/SmallField/RenormCondStep.lean`, `Def6.renormCondAlong_of_system`.

## 1. The system and the four clauses

Unknown `ξ = (ξ₁,ξ₂,ξ₃)` (`ζ = εξ₁`, `e = βξ₂`, `b = βξ₃`). The system is `A(ξ,p) ξ + c̃(ξ,p) = f̃(ξ,p)`,
`A = Flow.matrixInfty` (complete backgrounds; `matrixSel` selects the `ν`-free matrix below `k₀`), `c̃` the
explicitly second-order terms (products `ξ₁ξ₃`, `εξ₁²`, second-order parts of the expansions, the `ξ`-dependence of
`a, v`), `f̃` the forcing from the unrenormalized new term (`SMALLFIELD.md` §3.2-3.4). Rows (after the divisions
of P4 p. 714: (E1) by `βε`, (E2) by `β`, (E3) by `β`) are the conditions of `Def6.RenormCondAlong` on the
terms `Tm'` of the new level, with `Λ = (βε, β, β)`:

| row | equation | clause of `RenormCondAlong` | unknown |
|---|---|---|---|
| 1 | (E1) `∂_u f_u(1,v,0) − β(1+ξ₃)a_u(ζ²+ζ) + β ∂_u c₂ = 0` | `dpsi`: `d/dt ElocInf(0; (1+t)e, e)|₀ = 0` | `ζ` |
| 2 | (E2) `∂_b f_u · e₁ + βξ₂ + β ∂_b c₂ · e₁ = 0` | `dh`: `∂_h ElocInf(0; e, h)[e] = 0` (needs `ν' > 0`) | `e` |
| 3 | (E3) transversal second moment | `moment`: `lim_n momentSum(Tm'(idx n)) = 0` | `b` |
| — | additive constant `E^{(k+1)}` | `val`: `ElocInf(0; e, e) = 0` | not in `ξ` |

`val` is the first condition, "satisfied by the choice of the additive constant" (P4 p. 708): it is not a row.

## 2. How the counterterms enter the terms

New level density (`SPINE-PLAN.md` A4-1c): `D_E = ℰ''₀(θ_ξ) + oldE + C₁ − C₂ − vac` with `θ_ξ = (1+ζ(ξ))ψ`,
`ζ = ε ξ₁` (`renThetaDatum`), and by Lemma 3.5 (i) (`lemma35_i_complete(_bg)`) the action at the renormalized
datum is `β A(ψ,φ) + β(C₁ − C₂)`, `C₁ = renormC1` (explicit at the old background, linear in `ξ₃, ζ, νξ₂` plus
`ζ²`), `C₂ = renormC2` (quadratic in `δφ = φ_u − φ`, `δφ` the solution `F` of `IsRenSol`, `‖δφ‖ ≤ 8K₂ε‖ξ‖`).
The terms `Tm'` are the localized expansions of `D_E` (`thm31g_Eu/C1/C2_of_input`). The relevant parts of `Tm'`
(value, `∂_ψ`, `∂_h` at the constant field; the second moment) are therefore analytic functions `R_i(ξ)` of `ξ`:
the linear (in `ξ`) part of `R_i` is the row `i` of `A ξ`, with the matrix entries of Lemma 3.1; the rest of `R_i`
is `c̃_i − f̃_i`, where `f̃` is the value of the same parts at `ξ = 0` (only `ℰ''₀` and the old terms contribute)
and `c̃` the part vanishing to second order.

## 3. The bridge (exact signature)

```lean
theorem Balaban.SmallField.Def6.renormCondAlong_of_system
    {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} (m₀ : ℕ) (νk : ℝ)
    (Tm' : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (j : ℕ) (idx : ℕ → ℕ)
    (hidx : ∀ n, idx n ≠ 0)
    (A : Matrix (Fin 3) (Fin 3) ℂ) (ξ c f Λ : Fin 3 → ℂ) (hsys : A.mulVec ξ + c = f)
    (hval : ∀ i₀ : Fin N, ElocInf m₀ Tm' j 0 (constInf (Pi.single i₀ 1)) (constInf (Pi.single i₀ 1)) = 0)
    (hpsi : ∀ i₀, deriv (fun t : ℂ => ElocInf m₀ Tm' j 0 (constInf ((1+t) • Pi.single i₀ 1))
              (constInf (Pi.single i₀ 1))) 0 = Λ 0 * (A.mulVec ξ + c - f) 0)
    (hh : ∀ i₀, 0 < nuIdeal L k νk j → fderiv ℂ (fun h => ElocInf m₀ Tm' j 0 (constInf (Pi.single i₀ 1))
              (constInf h)) (Pi.single i₀ 1) (Pi.single i₀ 1) = Λ 1 * (A.mulVec ξ + c - f) 1)
    (hmom : ∀ i₀ i₁, i₀ ≠ i₁ → Tendsto (fun n => momentSum m₀ (Tm' (idx n)) j i₀ i₁) atTop
              (𝓝 (Λ 2 * (A.mulVec ξ + c - f) 2))) :
    RenormCondAlong m₀ k νk Tm' j idx hidx
```
Use at the step `k → k+1`: the class level of `Tm'` is `k+1` and `j = k+1`, `νk = ν'_{k+1}`; at `k = 0` the same
with the first step's terms. `(A, ξ, c, f)` are exactly the output of `Flow.rg_step_infty` /
`Flow.baseRg_step`: `hsys` is its equation `(A p).mulVec (ξs p) + c (ξs p, p) = f (ξs p, p)`.

Proof: the residual `A ξ + c − f` is `0` (`sub_eq_zero`), so the right sides vanish. The hypotheses are not
source premises but the definitional identities of the construction of `Tm'`:

* `hpsi`, `hh`, `hmom`: "the relevant part of `Tm'` is `Λ_i` times the `i`-th residual", for the `ξ`
  that parametrizes `Tm'`. They hold for every `ξ` in the polydisc by construction, and are used at the
  solution. To discharge them one proves (not done): (a) the `ξ`-dependence of `Tm'` through `θ_ξ`, `C₁`,
  `C₂` (Lemma 3.5, landed); (b) differentiation of `ElocInf` under the sum (`Einf_norm_le`, `IsSFFamily`), giving
  the rows with the entries of `A` (the computation of P4 (5.10)-(5.14), `SMALLFIELD.md` §3.3, with the quadratic
  form at `ν`-complete backgrounds); (c) for `hmom`, `TorusIndep` of the new level (A4-1f) so that the torus
  sequence stabilizes, and the limit of the finite-torus sums.
* `hval`: resolved by W1146u (A4-1g). The vacuum constant is not a term of `Terms`; it lives outside, as
  the vacuum constant `SFData.E`, with the record flow `ΦE` / `vacExt` (`Spine/SFStep.lean`, the clause
  `SFVacuumInput`, A4-1g). The level-`(k+1)` `Terms` of the general step map `Φ` are the shifted family: the
  labels are `f' = f − f(p₀)` at the unit constant configuration `p₀`, the per-block constant being moved
  into `E_{k+1}`. So `hval` holds for `Φ`'s own terms, and `renormCondAlong_of_system` is applied to `sf'.Tm`
  directly. `hpsi`, `hh`, `hmom` concern the shifted density `𝒟' = densE0 − densE0(p₀)` and are unaffected
  by the shift, since derivatives kill the constant.

## 4. Order of work after the bridge
1. `hpsi/hh` as identities in `ξ` for the zero class (`k = 0`): expansions of `ℰ''₀(θ_ξ)` (blocker 6 inputs).
2. `hmom` with `TorusIndep` (A4-1f, `BaseTwoTorus*` at `k = 0`).
3. `Flow.baseRg_step` + `baseCoeffBounds` (orchC-rg1b) give `ξ⁰` and `CoeffBounds`; the bridge gives `RenormCondAlong`;
   together `SFRenormQ` at `k = 1`.
