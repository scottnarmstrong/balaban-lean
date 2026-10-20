# KF0-FR — the case `k_f = 0` by finite-range whitening (route FR)

Route FR proves the spine input `KfZeroInput` (A7, LF-8 (b)) directly, without the split of
`kfZeroInput_of_parts` into a good sector (A7-1) and a bad sector (A7-2): the two sectors are never
separated, and the physical threshold of A7-1 (a) does not occur. The only condition beyond the
statement of `KfZeroInput` is a typing condition: the block side `s = M L` is large in terms of
`d, N, L, κ` (`KF0FRTyping`, §P). Lean status of each item is given at its end.

Notation. `Λ = 𝕋_ℓ`, `ℓ = s m`, blocks of side `s`; `n = N - 1 = dim h^⊥`; `7/8 L⁻² < ν ≤ 1`;
`K = -Δ + ν` on `Λ`; `A` the adjacency matrix, `K = (2d+ν) - A`; `q = 2d/(2d+ν)`;
`C = K^{-1/2} = ∑_n w_n A^n` (`kf0C`, entries `≥ 0`, row sums `ν^{-1/2}`); `C_R = ∑_{n ≤ R} w_n A^n`
(`kf0CR`, range `R`); `Q_R = C_R K C_R - 1` (`frQ`, symmetric, range `2R+1`, row sums of `|Q_R|` at most
`θ_Q := 2(4d+ν) ν^{-1/2} (2d+ν)^{-1/2} q^{R+1}/(1-q)`). The whitened field is `u = β^{-1/2} C_R ψ`.

## R. The representation (Lean: proved)

(R1) Two sheets. `S^{N-1} ∖ {equator} = Φ_+(B) ⊔ Φ_-(B)`, `B` the open unit ball of `h^⊥`,
`Φ_±(u) = u ± t(u) h`, `t(u) = √(1-|u|²)`, with the chart weight `w(u) = (1-|u|²)^{-1/2}`
(`integral_sphere_pi_sheets`). (R2) `H(Φ_σ(u)) = ½⟨u, K u⟩ + V_σ(u)` with
`V_σ = ½ ∑_{bonds} (s_y t_y - s_x t_x)² + (ν/2) ∑_x (s_x t_x - 1)²`, `s = ±1` the signs
(`energy_sheetCfg`). (R3) `u = β^{-1/2} C_R ψ`: `β ⟨u, K u⟩ = |ψ|² + ⟨ψ, Q_R ψ⟩`
(`tangentQuad_frField`), and the change of variables gives a standard Gaussian in `ψ`
(`integral_gauss_fr`). (R4) The sheets are drawn from a Bernoulli law `π_ε` (`ε = e^{-2βν}`) with the
compensating weight `b(false) = ε^{-1}` (`sum_sheets_eq_integral`). (R5) Hence
`Z(g) = c (1+ε)^{|Λ|} e^{⟨g,h⟩} ∫ ∏_t F_t dμ`, `μ = ⊗_x (γ ⊗ π_ε)`, with the site terms
`F_x = w(u_x) b(σ_x) e^{-(βν/2)(s_x t_x - 1)²} e^{⟨g_x, Φ_x - h⟩} e^{-½ ∑_y Q_R(x,y)⟨ψ_x,ψ_y⟩}` and the
bond terms `F_{x,μ} = e^{-(β/2)(s_y t_y - s_x t_x)²}`, `y = x + e_μ` (`partitionFunction_eq_terms`).
Every term is local: `F_x` depends on `ω = (ψ, σ)` in the ball `S_x = B(x, 2R+1)`, `F_{x,μ}` in
`S_{x,μ} = B(x, R+1)` (torus `ℓ¹` distance).

## J. Jacobians (Lean: proved)

(J1) `∫ w = |S^{N-1}_+|` (`lintegral_chartWeight_eq`). (J2) For a set `D` of sites with
`S_D = (β^{-1/2} C_R)|_{D×D}` invertible, integrating the variables of `D` with the others fixed,
`∫ ∏_x a_x(ω_x) ∏_{z ∈ D} w(u_z) dμ ≤ ∏_{x ∉ D} ∫ a_x · ∏_{x ∈ D} A_x · |det S_D|^{-n} (∫w)^{|D|}`
whenever `sup_ψ (∫ a_x(ψ,·) dπ_ε) γ(ψ) ≤ A_x` (`lintegral_jac_sites`); `γ(ψ)` is the Gaussian density.
(J3) `det (C_R)|_{D×D} ≥ (ν (2d+ν)^{-3/2})^{|D|}` (`det_submatrix_kf0CR_ge`, from the lower form
bound `C_R ≥ (1-q)(2d+ν)^{-1/2}`).

## G. One-site Gaussian estimates (Lean: proved, `KF0FRGauss`)

For `0 ≤ a`, `0 ≤ θ ≤ 1/8`, `r = |ψ|`, `γ(ψ) = (2π)^{-n/2} e^{-r²/2}`:
(G1) `γ(ψ) e^{a r + θ r²} ≤ (2π)^{-n/2} e^{a²}`;
(G2) `∫ e^{a r + θ r²} dγ ≤ 2^n e^{2a²}`;
(G3) for `a ≤ p/8`: `∫ 1[r > p] e^{a r + θ r²} dγ ≤ 2^n e^{-p²/8}`.
Proofs: `a r ≤ r²/8 + 2a²`, `1[r>p] ≤ e^{(r²-p²)/8}`, and `∫ e^{b r²} dγ = (1-2b)^{-n/2}`.

## O. Ordinary bounds (Lean: proved, `KF0FRBand`, `KF0FROrd`)

A site is *ordinary* if `|ψ_x| ≤ p` and `σ_x = +`. Put `ρ = p (βν)^{-1/2} ≤ 1/2` and
`G_x = ∑_i |g_{x,i}| ≤ G`.
(O1) If all sites of `B(x,R)` are ordinary, `|u_x| ≤ ρ` (`C_R ≥ 0`, row sums `≤ ν^{-1/2}`).
(O2) For `|u|² ≤ 1/4`: `1 ≤ w(u) ≤ 1 + |u|²`. (O3) `0 ≤ 1 - t(u) ≤ |u|²`. (O4) On the `+` sheet
`|Φ_+(u) - h| ≤ 2|u|`; always `|Φ_σ(u) - h| ≤ 2`.
(O5) If all sites of `S_x` are ordinary: `|F_x - 1| ≤ ε_site := 3(ρ² + βνρ⁴/2 + 2Gρ + θ_Q p²/2)` when
the bracket without `ρ²` is at most `1`; if all sites of `S_{x,μ}` are ordinary,
`|F_{x,μ} - 1| ≤ ε_bond := βρ⁴/2`.

## H. The heavy bound (Lean: proved, `frHeavy_le`; `KF0FRHeavyPt`, `KF0FRHeavySite`, `KF0FRHeavyD`, `KF0FRHeavyDInt`, `KF0FRHeavy`)

In Lean the inner-band constant is `2` instead of `2/√3`, `c_b = 1/128` (`t < 7/8` off the band), and
`θ = 8^k e η`.

Fix terms `C`, `W = ∪_{t∈C} S_t`, `H ⊆ W`; the event `E_H`: the sites of `H` are not ordinary, the
sites of `W ∖ H` are. Let `C_H = {t ∈ C : S_t ∩ H ≠ ∅}`; `|C_H| ≤ k|H|` with
`k = (1+d)(4R+3)^d` the multiplicity of the supports (each site lies in at most `k` of them).
Claim: `∫ 1_{E_H} ∏_{t∈C_H} |F_t - 1| dμ ≤ θ^{|H|}` with
`θ = (8/√3)^k e η_h`, where `η_h` (below) is the smallness of one heavy site.

(H1) Band split. `w(u) b(σ) e^{-(βν/2)(s t - 1)²} ≤ (2/√3) Λ(σ) + w(u) Λ'(σ)` with `Λ(+) = 1`,
`Λ'(+) = e^{-c_b βν}`, `c_b = (1-√3/2)²/2`, `Λ(-) = Λ'(-) = ε^{-1} e^{-βν/2}` (split at `|u|² = 1/4`).
(H2) Source: `|e^{⟨g_x, Φ_x - h⟩}| ≤ e^{2G|u_x|} e^{2G 1[σ_x = -]}` and
`2G |u_x| ≤ 2 c_G ∑_y C_R(x,y) |ψ_y|` for `G = c_G √β`.
(H3) Defect rows (AM–GM, `Q_R` symmetric): for a set `D` of sites,
`-½ ∑_{x∈D} ∑_y Q_R(x,y) ⟨ψ_x, ψ_y⟩ ≤ ½ θ_Q ∑_{y ∈ W'} |ψ_y|²`, `W' = ∪_{x∈D} S_x`.
(H4) Expansion: `∏_{t∈C_H}(1 + |F_t|) = ∑_{A ⊆ C_H} ∏_{t∈A} |F_t|`; bonds have `|F_t| ≤ 1`; with
`D` the sites of the site terms of `A`, (H1)–(H3) give on `E_H`
`∏_{t∈A}|F_t| ≤ ∑_{D' ⊆ D} ∏_{x ∈ D∖D'} (2/√3) Λ̃(σ_x) ∏_{x∈D'} Λ̃'(σ_x) w(u_x) ∏_{y∈W'} e^{a|ψ_y| + θ_Q|ψ_y|²/2}`,
`a = 2 c_G ν^{-1/2}`, `Λ̃ = Λ e^{2G 1[-]}`, `Λ̃' = Λ' e^{2G 1[-]}`.
(H5) Each `D'` is integrated by (J2) with `D := D'`; with `J = (√β/c₀)^n |S^{N-1}|`,
`c₀ = ν(2d+ν)^{-3/2}`, and (G1)–(G3), a heavy site costs at most
`η_h = max{(2π)^{-n/2} e^{a²}(e^{-c_bβν} + e^{-βν/2+2G}) J, (2/√3)(2^n e^{-p²/8} + 2^n e^{2a²} e^{-βν/2+2G}), 2^n e^{-p²/8} + ε 2^n e^{2a²}}`,
an ordinary site of `D'` at most `(2π)^{-n/2} e^{-c_bβν} K₀ J ≤ 1`, an ordinary site of `D ∖ D'` at
most `(2/√3) K₀`, an ordinary site of `W'` at most `K₀ = e^{ap + θ_Q p²/2}`. With
`|D| ≤ k|H|`, `|W'| ≤ k s^d |H|` and `K₀^{k s^d} ≤ e`, each `A` gives
`(4/√3)^{k|H|} e^{|H|} η_h^{|H|}`, and the `2^{k|H|}` sets `A` give the claim.

## M. The product bound of the Mayer weights (Lean: proved, `norm_integral_prod_frF_le`)

`norm_integral_prod_le_marks` (`Polymer/MarkBound.lean`) with the ordinary sets above, the supports
`S_t`, `ε_t ∈ {ε_site, ε_bond}`, the multiplicity `k` and (H):
`|∫ ∏_{t∈C} (F_t - 1) dμ| ≤ ∏_{t∈C} b_t`, `b_t = (1+√θ)^{|S_t|}(ε_t + θ^{1/(2k)} |S_t|)`.

## B. The block gas (Lean: open)

The terms are regrouped by their block support `X = bsup t` (blocks meeting `S_t`):
`f_X = ∏_{bsup t = X} F_t - 1`. Then `∫ ∏_t F_t dμ = ∫ ∏_X (1 + f_X) = Ξ(K)`
(`mayerGen_integral_eq`), and from (M), expanding `∏_X f_X` into products over nonempty subfamilies,
`|∫ ∏_{X∈𝒞} f_X| ≤ ∏_{X∈𝒞} (∏_{bsup t = X}(1+b_t) - 1)`. A block support lies in the `3^d` block box
of the base site (`2R+1 < s/2`), so its Steiner size is at most `3^d` and it carries at most
`(1+d) 3^d s^d` terms; hence the product bound of `mayerGen_activity_bound` holds with
`H₀ = (1+d) 3^d s^d b_* e^{(κ₀+κ₁) 3^d}`, `b_* = max b_t`. The Steiner geometry of `KF0AllGoodGas`
(G1–G3 with `c = 0`, `c₁ = 1`, `K₀ = 4e^{-κ₀}`) and `pe_size` give
`Ξ = exp ∑_Y P(Y)`, `∑_{Y ∋ b} |P(Y)| e^{κ' |Y|_St} ≤ α`.

## A. Analyticity (Lean: open)

Every product `∏_{t∈A} F_t` is `P_A(ω) exp(∑_{x,i} g_{x,i} V_{x,i}(ω))` with `P_A` independent of `g`
and `|V| ≤ 2`; `g ↦ ∫ P e^{⟨g,V⟩}` is entire when `P` is integrable (exponential series and
Weierstrass). So `K(Y; ·)` is analytic on the ball `∑|g| < G`, with the uniform Kotecký–Preiss bound,
and `P(Y; ·)` is analytic there (`pe_PY_analyticOnNhd`).

## S. Increments (Lean: open)

For `F` analytic on `{∑|g| < G}` with `|F| ≤ B`: `|F(g) - F(0)| ≤ 3B/G` on the unit ball (Schwarz on
`λ ↦ F(λg)`). With `G = c_G √β` the increments carry `β^{-1/2}`, which pays `c₉`.

## T. Two-torus agreement (Lean: open)

`C_R` and `Q_R` are polynomials of degree `≤ 2R+1` in `A`; on two tori of sides `> 4R+2` they agree at
pairs with equal centred displacement (`kf0CR_torus_eq`). Polymers in the quarter box correspond
(`polymer_lift`), the terms with block support inside them correspond and agree on related
configurations, and the local terms agree (`PY_mayer_transport`, general weights).

## P. Parameters (Lean: open)

`R = ⌊(s-3)/4⌋`, `k = (1+d)(4R+3)^d`, `p² = 8(2k log(9 s^d/b_*) + log(4^N e))`; `b_*` is fixed by the
gas numerics at `κ' = κ` (`κ₀ = kf0K0 d`, `κ₁ = κ + κ₀ + 5/2`). The typing condition: `θ_Q p² k² s^d`
small (`KF0FRTyping`), which holds for `s ≥ s₀(d, N, L, κ)` because `θ_Q ≤ C_d L³ e^{-7(R+1)/(8(2d+1)L²)}`
decays exponentially in `s/L²` while `p² k² s^d` grows polynomially. Then `c_G` is fixed by
`ap ≤ b_*/(32e)` and `ap k s^d ≤ 1/2`, and `β₀` by the `β`-small terms and by `3α/G ≤ (c₉/2) L^{-((d-2)/2+δ)}`.
