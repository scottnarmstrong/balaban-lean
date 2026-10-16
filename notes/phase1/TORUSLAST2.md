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
