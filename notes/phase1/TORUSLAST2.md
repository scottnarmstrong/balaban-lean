# TORUSLAST2 — blocker 7 at the last scale: walk-expansion reading and the redistribution design (W836)

No Lean. Labels: PROVED (landed Lean or arithmetic), SOURCE (read in the account), OPEN, REFUTED. Account = Yang--Mills-LLM-experiment,
https://github.com/ethanwsussman/Yang--Mills-LLM-experiment (part I: Def. non-wrapping I:57280ff, Def. admissible sites I:57027ff,
Theorem 4.38 I:58187ff, "intrinsic" clause I:58285-58325, floor I:57044-57049). Read as data only. Notation: ell = torus side in coarse
units of the last grid, q = ell/M (cells of the last scale), `finalOp = a Psi^{-1}`, `Psi = 1 + a Q X Q*`, `X = (N^2(-Delta)+v)^{-1}`.
## 1. What the account does (SOURCE) and why it does not transfer verbatim
**SOURCE.** Thm 4.38(ii): each term is a sum over footprints Xhat of walk-expansion terms E(Xhat; ...), each a function of data on Xhat;
for non-wrapping Xhat (cube of side <= s_j/4) the term is evaluated on the lift and is torus independent; wrapping Xhat carry the rest.
The total is a sum of such terms because the objects expanded are LINEAR in the walk expansion (Hessians, minimiser maps).
**REFUTED (reading, for the brief's U_Y).** The operator "sum over walks inside Y(C)" is the Dirichlet truncation U_Y of the lifted
operator to Y(C). It is torus independent, but `finalOp - U_Y` on `Y(C)^2` is not exponentially small: a walk from a coarse cell of the
boundary of Y(C) leaves Y(C) with probability bounded below by a constant depending on `d, L` only (one step out and back already
contributes a fixed fraction), so the difference is of order one near `dY(C)` and small only at distance t cells from it, like
`e^{-c M t}`. The coefficient `coef_C` reads all of `Y(C)^2` (W791), so replacing finalOp by U_Y changes each `T(C)` by order
`P/(e^kappa - 1)^{|C|}` with no small factor, and the identity is not recovered by any chain of 'walks leaving Y(C)'.
**REFUTED (as an expansion).** `Psi^{-1} = sum (-a Q X Q*)^n` does not converge: `||a Q X Q*||` can be `a/v <= 16 L^2/7 > 1`
(mass window `v > 7/(8L^2)`). So finalOp is not a Neumann series in the walks of X; and `coef_C` is not linear in finalOp
(log det, Stieltjes square root), so a footprint decomposition of `T(C)` into torus independent pieces would need a second, nested
expansion around a footprint-local base (telescoping over the regions Y_r(C), r = 0,1,...). None is landed.
## 2. Question (1): the correct lifted operator and the remainder
**PROVED (landed).** `unitOperator_eq_smul_inv_psi` (finalOp = a Psi^{-1}); the walk series of X (`kf0Adj_pow_eq_count`,
`X_entry_hasSum`); the Chernoff bound on bad walks `sum_bad_walks_le`, `X_sum_close`: block sums of X on tori of sides ell, ell' >= B + D
differ by `<= 6 d/v e^{-(sqrt v/(2N)) D}`, k-uniform since the rate is per coarse distance; `psi_entry_close`; `finalOp_entry_close_unif`
(`C c` depend on `d, L` only; all `k >= 1`; window `7/(8L^2) < v <= 1`, `1/2 <= a <= 2`).
**SOURCE/OPEN (not landed; not needed below).** A convergent walk expansion of `Y = (N^2(-Delta)+v+a Q*Q)^{-1}` exists: expand around the
block diagonal `D0 = (2dN^2+v) + a Q*Q` (inverse block local, signed); `||D0^{-1} N^2 A|| <= 2dN^2/(2dN^2+v) < 1` for each k, and the
Chernoff bound turns this into decay `e^{-(sqrt v/2N)D}` per coarse distance, uniform in k. Then `finalOp = a - a^2 Q Y Q*`, and by the method
of images (the operator is periodic) `finalOp_ell(x,y) = U_inf(x,y) + sum_{n != 0} (-a^2)(Q Y_inf Q*)(x, y + ell n)`, with `U_inf` the
infinite-volume operator on the lift. **So the lifted operator is U_inf (all walks, unrestricted footprint) and the remainder is the sum over
WINDING walks (lift ends in `y + ell n`, `n != 0`)**, of size `e^{-c ell}` uniformly in k. This is the content of W807's closeness
(`finalOp_entry_close_unif`), proved there without the images formula. The footprint of a winding walk is wrapping: this is the account's mechanism.
**OPEN.** `U_inf` is not a matrix on a torus: W791/W807 take `U` on `L1Torus N`, with the coercivity and decay hypotheses of the cores.
A window copy of U_inf has none of them. Hence the design below does not use U_inf (use a finite torus whose size depends on the support).
## 3. Question (2): the design and the identity
**Definition (inside the proof of Root-F; no new Lean definition).** For a support `A` (finite set in the quarter box) put
`ell_can(A)` = the least multiple of `M L^{kf+1}` with `ell_can >= 8 (width(A) + 6 M)`, a function of A and the fixed data only. For `X` in
`Q_ell` (image of such A) set `T^new_{ell,j}(x,X;g) := T^old_{ell_can(A),j}(x_can, X_can; g transported)`. This is ell-independent on
`Q_ell` by construction, so the clause holds identically. (The same formula on every torus, with the torus chosen by the support.)
Only W791's matrix part is used in the form with `eta > 0` (W807); W791's exact form (hU, hE identities) is NOT used, because
`finalOp_ell != finalOp_{ell_can}` on `Y(C)^2`; with `U_inf` the hypotheses would be identities but see the OPEN of section 2.
**The identity.** The sum over X of T^old changes by the difference `Delta(x,X) = T^old_ell(x,X) - T^new_ell(x,X)`, `X in Q_ell`. Put
`T^new_ell(x,X') += Delta(x,X)` where `X' = X u chain(X)`: a fixed (lexicographically first) path of scale-j blocks from X out of the box
`|y_mu| < ell/4`. Then `X' notin Q_ell` (no clause), `X'` is a polymer containing x (support), `Delta` depends on `g|_{Y(C)}` (locality),
analytic (differences of analytic terms), and the total sum is unchanged: **a resummation into polymers containing a chain to the
wrapping region, not a telescoping over nested regions.**
**Bound.** PROVED ingredient (W807, k-uniform): for the final coefficients (`final_coef_logdet_close_twoTorus_unif`,
`final_coef_cutoffInteraction_close_twoTorus_unif`) `|coef_C[finalOp_ell] - coef_C[finalOp_ell']| <= P (C0 e^{-c0 (min/2 - (J+3)M)} + eps_E)/(e^kappa-1)^{|C|}`
under `2(J+6)M <= min(ell, ell')`, with `M >= 4 pdB e^{pdH kappa}` and `8 kappa 7^d <= pdEps M`: M is chosen after kappa, L, as in Root-F.
If C has t cells between it and the box edge, `Delta <= e^{-c M (t-6)}` against the chain cost `e^{-kappa (t+1)}`: fine once `c M >= kappa + 1`.
For the edge band `t <= 6` there is no smallness; there the crude bound `2 c9' e^{-kappa' |C|}` pays for a chain of at most 7 cells if the old family
is built with `kappa' = 8 kappa + 2` (absolute constant, independent of L). **OPEN (hierarchy):** Root-F quantifies `kappa, c9` before `L, M`,
so no L-dependent loss can be absorbed; the construction therefore needs the old (torus-clause-free) family at parameters `(8 kappa + 2, c9/2)`,
and the entropy `2^{|X'|}` of the map `(C) -> X'` goes into the same margin. Not checked against ROOTBOUND.md.
**OPEN (inputs not covered by W807).** `hFclose`: the physical functional F entering the last integral (the output of steps <= kf) must
correspond on `Y(C)` between ell and ell_can; this is the same redistribution one level down (induction on scales), and W802 lists its Lipschitz
constant as open. Also the large-field polymer terms P9 of scale kf+1 and the other `M_n` terms: their torus dependence is only through
finite range reads (exact, W666/W678) with margin `C L s_j` that is L-dependent, see section 4.
## 4. Question (3): the floor
**PROVED (arithmetic, from the frozen text).** `Frozen/Roots/LogPartitionMultiscale.lean` carries only `M L^{kf+1} | ell` and the quarter box;
`kf` is fixed by `nu` alone, not by ell. So `ell = M L^{kf+1}` (q = 1) is allowed. The clause is vacuous there at `j = kf+1` (W796 count: q <= 3) but
NOT at `j <= kf`: for `j = kf`, `L >= 4`, the block `[0, M L^{kf})^d` has `max y < M L^{kf+1}/4`. So the quarter-box condition plus kf and the cell size
do not imply a floor; the gap `4 <= q <~ C L` of TORUSLAST s3 remains at the last scale, and at `j = kf+1-i` for `q L^{i} <~ C L`, i.e. the top
`O(m0 + m1 + ...)` scales (C = 19 L^{m0+...} of W678).
**Comparison with the account (SOURCE).** Floor `L^{m+K'-i} >= L^{11} M Rcheck_i`, i.e. `ell >= 2 L^{11} Rcheck_i M L^i` at level i; at the last level
`q >= 2 L^{11} Rcheck`. This beats `q > C L` only if `19 L^{m0+...} <= 2 L^{10} Rcheck`: OPEN numerically (needs the exponents m0, m1 of W678 and Rcheck).
Adding a floor to Root-F changes a frozen statement: report to Scott/Roland, do not edit.
**Consequence of the design.** At the last scale (absolute margin 6 cells from `2(J+6)M <= ell`) the redistribution needs no floor: tori with q < 20 are
all 'edge band' and cost a chain of at most 20 cells, an absolute constant. At scales `j <= kf` in the gap the margin band is `C L` cells of size `s_j`,
L-dependent; the crude bound cannot pay `e^{-kappa C L}` (by the hierarchy above), so either those terms are exactly torus local with an absolute margin
(the account's claim; not proved here) or a floor is needed. This is the exact obstruction for `j <= kf`.
## 5. Recommendation and leaves (each <= 300 lines, no new definitions)
Recommendation: do NOT build U_Y / U_inf as new operators. Use the canonical-torus resummation (section 3): it uses only W807 and needs no new definition
(`ell_can` is a choice inside the root proof). Treat `j <= kf` in the gap and `hFclose` as the remaining blockers; ask for the floor if the margin cannot be made absolute.
1. **Translation covariance** of `finalOp` and of the cell maps: `finalOp (x+t)(y+t) = finalOp x y` for coarse translations (check `Green/TranslationInvariant.lean`
   first); W791/W807 use a one-sided window `[2M,(J+3)M]`, the clause a two-sided box. ~150 lines.
2. **Packaged last-scale closeness** `finalCoef_close_quarterBox`: the two W807 theorems combined for `C` at margin `t >= 7` cells of the quarter box of ell,
   with `ell_can`; conclusion `|Delta| <= P' e^{-c M t}` with explicit `kappa`-free constants. ~200 lines.
3. **Edge band bound**: `|T^old| <= c9' e^{-kappa' |C|}` transferred to `X'`; arithmetic with `kappa' = 8 kappa + 2`. ~120 lines.
4. **Chain geometry**: existence of a canonical connected union of `<= t+1` blocks from X to outside the quarter box, `IsPolymer`, injectivity up to `2^{|X'|}`. ~250 lines.
5. **Abstract assembly**: from families `T^old_ell` (support, locality, analyticity, bound, identity) and the closeness hypotheses (leaves 2, 3), produce `T^new` with the
   Root-F clauses incl. the torus clause. Hypotheses are source premises only. ~300 lines.
6. **Gap scales** (OPEN, no leaf yet): the corresponding closeness or exact locality for the finite-range ingredients of `j <= kf` with an absolute margin.
Obstruction summary: U_Y by walks inside Y(C) is not close to finalOp; the closeness that is true is for the full lift (winding remainder, W807), usable through a support-dependent
canonical torus. Not settled: hierarchy of constants, `hFclose`, the gap scales `j <= kf`.

W837 status (leaves 1 and 2, landed in `Balaban/Polymer/TwoTorusQuarterBox.lean`): leaf 1 PROVED: `finalOp`, macro cover (`macCell/macBox/macChi/macTags`), `taggedGfin/taggedCfin` and the log-det matrix are covariant under coarse translations by `p` cells; `final_coef_logdet_close_twoTorus_box` and `final_coef_cutoffInteraction_close_twoTorus_box` are the W807 theorems for supports with shifted indices in `[4, J]` (hypotheses on `F`, `gamma`, `E`, `ell` in the original, unshifted frame; analyticity of the interaction is taken from `cutoffInteraction_final`).
Leaf 2 PROVED: `finalCoef_close_quarterBox` (and the separate `finalCoef_logdet_close_quarterBox`, `finalCoef_cutoff_close_quarterBox`): support within `m` cells of the origin, `4(m+t) <= K`, `t >= 5`, tori `N <= N'` multiples of `M`; bound `P(C0 e^{-c0 M (2t-7)} + eps_E)/(e^kappa - 1)^{|C|}` (cutoff: W807's prefactor with `e^{-c0 M (2t-7)}`), `P, C0, c0` uniform in `k`. Exponent is `2t-7` not `t-6`: the quarter box is `K/4` cells, window `J = 2m+4`, `K/2 - (J+3) >= 2t-7`.
Not done: leaves 3-6; `hFclose` and the gap scales `j <= kf` as before; existence lemmas `exists_residueMap_box`, `exists_cellMap_box` give `f`, `e` for `N <= N'`.

W843 status (leaves 3 and 4, `Balaban/Polymer/TwoTorusEdgeChain.lean`): leaf 4 PROVED at the block level: `exists_edgeChain_map` (box of radius r, 2r+2 <= K; polymer Y with a cell within t of the edge in some coordinate; straight chain in that coordinate; `Phi Y` a polymer, `Y <= Phi Y`, `|Phi Y| <= |Y| + t + 1`, a cell outside the box, at most `2^|Z|` preimages of each `Z`); frozen form `edgeChain_isPolymer` (`IsPolymer`, size `|X'|/s^d <= |Y|+t+1`).
Leaf 3 PROVED as arithmetic: `edgeBand_fiber_bound`: crude rate kappa' in |Y| gives `c e^{kappa'(t+1)} e^{-kappa|Z|}` on the preimage sum iff `kappa + log 2 <= kappa'`; `edgeBand_fiber_bound_rate` is kappa' = 8 kappa + 2 (any kappa >= 0). The crude bound `||T Y|| <= c e^{-kappa'|Y|}` is the input (from `detRatioCoef_decay` etc.); not transferred here.

W845 status (leaf 5, `Balaban/Polymer/TwoTorusResum.lean`): PROVED the abstract assembly `resum_lastScale` (terms `T ell g X` on `X in P ell`, canonical torus `can X`, chain map `Phi ell`; new terms = `T (can X)` in the quarter box, old term plus the differences of the preimages outside): (a) sum preserved, (b) exact torus independence, (c) bound `(B + a e^{kappa'} + 2B e^{kappa' t0}) e^{-kappa |X|}` for `kappa + log 2 <= kappa' <= lam`, (d) support, locality, membership in a function space `W` (analyticity).
Instance: `quarterBox_rate` (bound of `finalCoef_close_quarterBox` to `a e^{-lam t} e^{-kappa' n}`), `resum_lastScale_of_quarterBox`, frame `macIdx_torus_frame` (MacIdx cells = `Torus d K` cells, box condition preserved).
Still physical: `hFclose` as the decay `eps <= eps1 e^{-lam tau}` of the operator closeness on the support, gamma-correspondence and the maps `f`, `e`, identification of `T` with sums of coefficients over `C` with `Y(C) = X` (entropy of the fibres), the crude bound with `kappa'`, `hfib` from `exists_edgeChain_map` for the margin-dependent chains; gap scales `j <= kf` unchanged.

W846 status (`Balaban/Polymer/TwoTorusResumInstance.lean`): PROVED `lastScale_chain` (one map `Phi ell` on supports = polymers of `Torus d (K ell)` in centred coordinates `valMinAbs`, quarter box = all |coordinate| <= K/4, margin tau = K/4 - max|coordinate|, chain length tau+1 from `exists_edgeChain_map`; gives hPhiP, hPhisz, hfib, hRPhi, hAgPhi). The fibre is <= 2^|Z| with NO margin factor (Phi ell X depends on X only and contains X), so the rate condition stays `kappa + log 2 <= kappa'`.
Order: `can X` must satisfy `K ell <= K (can X)` (hcanK); then `X in P (can X)` is a theorem (`quarterBox_polymer_larger`) and the closeness is used in the order of `finalCoef_close_quarterBox` (smaller torus first, its margin). `resum_lastScale_torus` = `resum_lastScale_of_quarterBox` with all chain/order hypotheses discharged.
Crude bound arithmetic: `rate_of_kappa_large`, `exists_kappa_large`, `detRatioCoef_decay_rate` (kappa' <= log((e^kappa1-1)/2) once 2e^kappa'+2 <= e^kappa1). Still physical: the identification of T with coefficient sums, hcoef (apply finalCoef_close_quarterBox with m+t = K/4), eps decay, and a family of tori with a canonical largest torus.

W847 status (blocker 7, limit at the last scale): `Polymer/TwoTorusResum.lean` now has `resum_lastScale_target` (target function V in place of `T (can X)`); `resum_lastScale` is an application (statement unchanged).
`Polymer/TwoTorusResumLimit.lean`: `lastScale_limit` (Cauchy, V := limUnder, closeness to every torus, bound, support, locality, uniform convergence on D), `analytic_closed_under_uniform_limit` (W = analytic on open D), `resum_lastScale_limit` (assembly for an unbounded family tor : ℕ → ι).
Open for the instance: Le (order on tori), the eventual-box hypothesis `hev`, margin tending to infinity `hτ`, and the closeness `hcoef` between the smaller and a larger torus must be supplied for Root-F's family.

W849 status (`Balaban/Polymer/TwoTorusResumRootF.lean`): PROVED the family hypotheses of `resum_lastScale_limit` for block tori (order `K ℓ ≤ K ℓ'`, `K` = cells of the last scale per side = side/(M L^{kf+1})): `rootF_hmono`, `rootF_hcof`, `rootF_hev` (via `quarterBox_polymer_larger`), `rootF_hτ`, `hWlim_analytic`, `rootF_cells` (Root-F sides to K facts), `rootF_hcoef_limit` (W846-form closeness to the limit form).
Assembled `resum_lastScale_torus_limit` (new terms = lim_n T (tor n) on every quarter box; sum, torus independence, bound, support, locality, analyticity). Physical inputs left as hypotheses: support/locality/analyticity/bound of T, the pairwise closeness `hcoef` in the form of `finalCoef_close_quarterBox` with the operator closeness `eps` and its decay `hε` (hFclose), identification of T with coefficient sums.
Not done: gap scales `j <= kf`, the identification of T with the coefficient sums (entropy of fibres).

W850 status (`Balaban/Polymer/TwoTorusFibre.lean`): PROVED the fibre of the last-scale term: `T ℓ g X = Σ_{C : C.image (cen ℓ) = X} cf ℓ g C` with `cen` the centred coordinates of the cells; `fibre_unique`, `fibre_card_le` (at most one set, a fortiori `2^|X|`; no loss in κ'), `fibre_closeness` (closeness of one coefficient, in the form of `finalCoef_close_quarterBox`, gives the form of `hcoef`, same κ).
`fibre_hcoef_of_quarterBox`: T = Σ (coef ellE - coef ell0 + coef J) from `finalCoef_close_quarterBox` (physical inputs listed as hypotheses: WSmall, analytic logarithms, hEcl, hFcl, hγ, bounds Lb, mb). OBSTRUCTION: P, C₀, c₀ of the landed theorem depend on nC (a bound on |C|), so hcoef holds for |X| ≤ nC, not uniformly in X as `rootF_hcoef_limit` needs.

W854 status (blocker 7, uniformity in the support size; no Lean change): only P depends on nC (C₀, c₀ do not). In `final_taggedGfin_close`, `final_coef_logdet_close_twoTorus_of_entries`, `final_coef_cutoffInteraction_close_twoTorus_of_cfin` the dependence is P ~ nC^4 e^{κ nC} (Gfin/CfinU, then × |Y| ≤ nC (8M+1)^d in the cutoff clause) and P ~ nC^3 e^{κ nC} (log-det), with nC replaceable by |C|.
The polynomial part is harmless; the factor e^{κ|C|} is not: it comes from `taggedMat_close_twoTorus` (tag monomial ≤ e^{κ|C|}, absolute closeness ε of the entries), and e^{κ|C|}/(e^κ-1)^{|C|} has no decay in |C|, so `rootF_hcoef_limit` (needs κ' ≥ κ + log 2) cannot use any nC-free statement obtained by making |C| explicit.
Repair (not done, changes the interface): |tagMon| ≤ e^{H κ} e^{κ 7^d dist(x,y)/M} (macTags_card_le) and interpolate min(ε, 2D e^{-σ dist}) ≤ √(2Dε) e^{-σ dist/2} for the entries of U-U' and E-E' (needs dist(f x, f y) = dist(x,y) on Y(C)); this gives a bound polynomial in |C| but with √ε in place of ε (decay rates of ε halved), or linear ε if the operator closeness is supplied with a weight e^{-σ dist}.

W855 status (blocker 7 repair, first leaves, `Balaban/Green/FinalTaggedWeighted.lean`): `final_region_entry_close_weighted` (entry difference ≤ √(2D·C₀e^{-c₀(min N N'/2-(J+3)M)}) e^{-σ dist/2}, D = finalDecayC, σ = blockDecayRate, constants of the uniform closeness), `norm_tagMon_macTags_le` (‖tagMon‖ ≤ e^{Hκ}e^{κ7^d dist/M}), `dist_map_eq_of_mem_macRegion`.
`taggedMat_close_twoTorus_weighted`: with entry closeness δ e^{-σ dist}, tagged difference ≤ |C| e^{Hκ} δ e^{-(σ-κ7^d/M)dist}; `_le`: ≤ |C| e^{Hκ} δ when σ ≥ κ7^d/M. No e^{κ|C|}; landed `taggedMat_close_twoTorus` kept (its hypothesis is absolute, does not imply the weighted one).
Not done: rewiring `final_taggedGfin_close` etc. to the weighted version (needs the weighted hypothesis on the cell families a, a' of box resolvents, with decay rate σ > κ7^d/M, and the √ε loss from (1) for the operator entries).

W857 status (blocker 7, `Balaban/Green/FinalTaggedWeightedGfin.lean`): `final_boxFamily_close_weighted` (chi_z G_z and R_z differ by <= sqrt(A B) e^{-(pdEps/4) dist}, interpolating the absolute closeness with `boxG_final_entry_bound`, `boxR_final_entry_bound`; rate sigma'' = pdEps/4), `final_taggedGK_close_weighted` (|C| e^{pdH kappa} times that, from `hMk : 8 kappa 7^d <= pdEps M` which gives kappa 7^d/M <= pdEps/4), `final_taggedGfin_close_weighted` / `final_taggedCfinU_close_weighted` (<= P (nC^2+nC^4) sqrt(eps) (g+t)^-1, resp. / sqrt g; P independent of nC, no e^{kappa nC}).
Price: sqrt(eps) instead of eps (interpolation); linear eps would need weighted `rowmul_close`. Shared cores `final_taggedGfin_close_core`, `taggedCfinU_close_of_Gfin` (proof-body refactor of the landed theorems, statements unchanged).

W860 status (blocker 7, size-uniform coefficients; `Green/FinalCoefWeighted.lean`, `Polymer/TwoTorusFibreWeighted.lean`): `final_taggedKE_close_weighted` (|C| e^{Hκ}(δR+δE), δE from `final_boxE_close_weighted`, E decay rate rE >= pdEps/4, rate pdEps/8), log-det and cutoff clauses `..._unif_weighted` with P independent of nC (bound P nC^3 (sqrt eps0 + sqrt epsE)/(e^κ-1)^|C|, resp. P (nC^2+nC^4) sqrt eps0/sqrt g times nC (8M+1)^d). Shared cores: `final_coef_logdet_close_core`, `final_coef_cutoffInteraction_close_core`, `rowmul_close_core`; transport cores `..._box_of`, `..._quarterBox_of` (arbitrary bound, antitone in the exponent) in `TwoTorusQuarterBox`; landed statements unchanged.
`finalCoef_close_quarterBox_weighted`: no nC, denominator sqrt(e^κ-1)^|C| (polynomial absorbed, base e^{κ1}-1 = sqrt(e^κ-1)), sqrt εE; `fibre_hcoef_of_quarterBox_weighted`: hcoef of `rootF_hcoef_limit` with κ1, ε := sqrt ε (hε: `sqrt_le_sqrt_mul_exp_half`, lam halved; c₀ of the final operators is halved inside). Not done: wiring into the Root-F application (choose κ' <= log(e^κ1 - 1) = (1/2) log(e^κ - 1)).

W867 status (blocker 7 wiring; `Balaban/Polymer/TwoTorusResumWired.lean`): PROVED `resum_lastScale_rootF_weighted` (`fibre_hcoef_of_quarterBox_weighted` + `resum_lastScale_torus_limit`, T inline as in `hT`; ε := sqrt ε, κ₁ = log(1+sqrt(e^κ-1)), Mr = M; conclusion with output rate κo, crude rate κ', decay lam) and `rootF_rates_of_kappa_large` (2(κo+log 2) <= log(e^κ-1) for κ >= log(e^{2(κo+log 2)}+1)).
Physical hypotheses left: WSmall, analytic logs, hEcl/hFcl/hγ, hT, support/locality/analyticity of T, crude bound hbd (rate κ'), hε (rate 2 lam). Not controlled: lam <= 2 c₀ M (c₀ is existential after M is fixed; not shown M-independent).
