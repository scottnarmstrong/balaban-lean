# LF4R plan: Lemma III.8.7 and Theorem III.8.9 of LF-RECONSTRUCTION against the landed Lean (W876, 2026-10-17)

Refute-first. Statuses: LANDED / PARTIAL / MISSING. Names checked in the worktree (branch w876-lf4r-plan).
Scope: the removed outcome (3.10'); the kept outcomes (a), (b) of III.8.9 are only mentioned where they share an ingredient.

## 0. Contradictions and gaps found in the reconstruction against the landed definitions
1. III.8.9 (c) says `C_R lam^{2d+1} <= A_2 lam^{p_2}` "by (Lambda10)". The landed (Lambda10) (`LamConditions.l10`, Counter/Conditions.lean:51) is
   `C_R x^{2d+1} + 2A_2(c''x)^{p_2} + ... + 1 <= A'_3 x^{p_R}` with `p_R > p_2 + 2d` (`Typing`, Params.lean:237). It does not give `C_R x^{2d+1} <= A_2 x^{p_2}`.
   True and needed: a separate large-x condition `C_R <= A_2 x^{p_2-2d-1}` (`p_2 >= 2d+3` is `p2_ge`). Leaf 1 takes it as `hCR`; leaf 3 adds it to the lambda_* conditions.
2. `C_R` is a free typing constant (`Typing.CR`, `CR_nonneg`). Definition III.8.6 ("least constant with (III.8.4)") is not landed; `Rep.rg_ripe` and `StepData.bound` use `S.CR` as an abstract number.
   The inequality (III.8.4) (L_res arithmetic) is MISSING and is a premise on the constants of rows 0-11.
3. Exponent scale. The gas consumer wants `exp(-p2Run - H|c_z|)`, `p2Run = A2 (log b_k)^{p2}` (running beta). (3.10') has `A2 lamHat_k^{p2}`. With `lamHat_k = log(beta a)+1+k theta`,
   `theta = (d-2) log L` (`thetaOf`) and `b_k = beta L^{k(d-2)} gamma`, `|log gamma| <= eps <= 1/20` (`RunningHyp.beta_eq`): `log b_k <= lamHat_k`, so `p2Run <= A2 lam^{p2}` is the right direction. Not landed as a lemma (leaf 3).
4. `H_k|Z|_k`: landed budget is `H_k * M^d * card` (`BudgetConsts.budgetG`, `cubeVol`). The gas wants `H * card (cz z)`; take `H := HRun H0 beta k * M^d`. Matches, but |Z|_k (blocks) vs card of cubes must be checked in leaf 3.
5. The reconstruction sums over localized histories `a` and says "summed by Lemma II.5.15". Landed: `Budget/Summability.lean` `sum_inv_logC_le_one`, `Budget/Labelled.lean` `sum_inv_logC_labelled`, `Budget/Injective.lean` (II.5.15). So sum_a e^{-logC(a)} <= 1 is LANDED; (3.10') for one history gives the sum with a factor e^{-logC(a)}, which needs `logC >= 0` (used in leaf 1, `hlogC`).
6. The window bound (III.8.5) is for the integral of K e^{Re b} over the outputs on Z and the internal variables. Landed `KerBound` is exactly this predicate with F = 1 (Operators/KerBound.lean:85). Therefore the removed operator must be an `LFKernel` on the same types as `(datum k a kappa).ker`, and (III.8.5) at gamma = 0 is `KerBound a k Trem (kappa^pre - C_R lam^{2d+1})` after `c1 >= C_W`, `c2 >= C'_W`.
7. Lemma III.8.2 physical: `denominatorPhysical_bounds` has only the crude `|E~_0| <= C_E~ D_0^d + 2 E n`; the sharp (3.6)-(3.7) is not proved. Enough for L_res (it is part of (III.8.4)), not for kept-outcome refinements. Q13: massless reference stays; nothing here is specific to A or A0'.

## 1. Ingredients of Lemma III.8.7 (removed outcome, gamma = 0)
| Ingredient | Status | Evidence |
|---|---|---|
| Decomposition of unity, K^pre = sum of outcome kernels, weights, C_dec = 5 | LANDED | `Outcome.lean`: `weight_sum`, `outcomeKernel`, `outcomeKernel_sum`, `cDec`, `sum_inv_cDec` |
| R on a representation, normalization (Lemma III.8.4), physical reference | LANDED | `Rop.lean` `Rop`, `RDecomp`; `RopNorm`, `RopConcrete*`, `RopPhysical` `R_normalizationPhysical`, `R_normalization_ripe` |
| Reference density rho_{k,0}, chi_{Z_0}, radius C_6 beta^{-1/2} p_0 | LANDED | `RhoZero` `rhoZero`, `cSix`, `zeroRadius`; `RhoZeroPhysical` `rhoZeroPhysical`, `massFunctional` |
| Denominator (Lemma III.8.2), massless and physical | LANDED / PARTIAL | `Denominator` `denominator_eq` (massless, exact); `RhoZeroPhysical` `denominatorPhysical_bounds` (crude E~_0 bound only) |
| Kernel K^(3.7) (3.7'), exponent b^(3.7), internal variables I^(3.7) | MISSING | no `kernel37`; only the abstract `RDecomp`/`Rop` and `LFKernel` (Operators/Kernel.lean). Needs the change of variables psi'' = psi~ - psi^0_{k1,k} (`Operators/GaussChange.lean`, `DomainIdentity.lean` are the nearest) and (2.58') |
| Removed operator T^rem as an object (LFKernel on the localized history of Z) | MISSING | `locOp`/`keptOp` (Operators/LocOp.lean) cover pre-operators and kept operators only; `RFieldProjection.lean` states the obligations (OPEN-R-PRESERVES-ISREP2), proves none |
| Window variables and their volumes (shell {|u.u-1|<3dL delta_j} and ball |psi''|<delta_{j,1}, volume <= 1, (Lambda17')) | PARTIAL | `QuietBound.lean` `shell_newOut`, `shell_newPrime` for the quiet step; nothing for psi'' or psi_{k1} on U~3 \ Z_{k1}; `ShellVolume.lean` (generic shell volume) |
| psi_k on Z^c_0 cap Z: spanning-tree balls of radius 3 delta_k (tilde chi_k), factor per block | PARTIAL | `SmallFactorChi.lean`, `ChiBridge*.lean` (tilde chi_k as a predicate); no volume bound per block |
| psi_k on Z_0 (ball radius C_6 beta^{-1/2} p_0 times beta^{N/2}) | PARTIAL | `RhoZero`/`RhoZeroPhysical` `rhoZeroPhysical_bounds`, `integral_rhoZeroPhysical_bounds`; the volume factor `v_N C_6^N A_0^N lam^{N p_0}` is not stated |
| Bounds e^{Re b_win} <= e^{sum (C_b log beta_j + C_b B_0)|X_j|} (S0); |e^{C_{k1,k}}| <= e^{C_15 sum|X_j|} (2.15') | PARTIAL | `QuietBound.lean` (quiet step, (S0) with c_1, c_2); `ActionConvWindow.lean` (window action theorem (2.15')); assembly over j in [k1,k) not stated |
| Pointwise bound e^{-G^# - A_win} const^#/const <= e^{-beta A*+1+3+|C^#_0|+C_{k1,k}} (2.58', Lemma III.6.4) | PARTIAL | `WindowGen*.lean` (2.17'), `Denominator*.lean`; the 2.58' identity for the removed outcome is not stated |
| |e^{E_k|Z|}| <= e^{(C'_E lam + C'_E)|Z|_k}, |Z|_k <= (M crit_k)^d | PARTIAL | `RRipeCard.lean` `removed_card_le` (<= crit_k^d cubes); the E_k bound is a premise (P7 p. 520) |
| (D5) at scale k1 for the core: prod_C int K_{k1}(C) e^{Re b_C} <= e^{-sum kappa_{k1}(C)} | LANDED (pre-operator form) | `Operators/CompBound.lean` `PkgBound`; `LocOpBound.lean` `locOp_pkgBound_kappa`. The core operators are `locOp` of the ancestors; the (1.26) form is `KerBound` |
| Small factors gamma_i of Lemma III.5.3 | LANDED, not used for rem | `SmallFactorGe.lean` `smallFactor_ge`; `HgeoDischarge.lean` `smallFactor_{one,two,five}_ripe`; gamma(rem) = 0 |
| L_res arithmetic (III.8.4) with C_R | MISSING (see 0.2) | |

## 2. Ingredients of Theorem III.8.9 (c) and (3.10')
| Ingredient | Status | Evidence |
|---|---|---|
| Budget G = kappa - log C - H_k|Z|_k, kappa^pre = sum kappa + kappaStep; c_1 >= C_W, c_2 >= C'_W | LANDED | `Budget/Exponents.lean` `budgetG`, `kappaPre`, `Gpre`; `QuietBound` (step exponent) |
| Ripeness `G^pre >= 2 A2 lam^{p2} + 1` | LANDED | `Counter/Main.lean` `CounterConclusion.Gp_ripe` (from `PreH6`, `Ripe`, Active gives nu >= 1) |
| (Rg) for kept components | LANDED | `Def7Basic.lean` `Rep.rg_ripe`; `Counter/Instantiation.lean` `toLF2Hyp` takes it as an argument |
| Sum over histories, combinatorial factor | LANDED | `Budget/Summability.lean` `sum_inv_logC_le_one`, `Budget/Injective.lean` |
| Exponent assembly (3.10') for one history from the window bound | LANDED (this W876) | `RRemovedFactor.lean` `removed_kerBound_logC_of_window`, `KerBound.mono`, `CR_pow_le_A2_pow` |
| Window bound (III.8.5) for rem | MISSING | leaf 6 |
| From the kernel bound to `‖tau z‖`: tau z := sum_a int Trem_a e^{E|Z|} F dpsi, F = the remaining factor with sup|F| <= 1; `‖tau z‖ <= sum_a sup|F| int absW` | MISSING | leaf 3 |
| Consumer | LANDED | `R/RGasCoreFinal.lean` `gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_run`, hypothesis `hrem : forall z, ‖tau z‖ <= exp(-p2Run - H*(cz z).1.card)` |

How tau of the gas is tied to the removed operator: for z with component cz z in Rem_k, tau z is the value, at the fixed outer data, of
`sum over localized histories a of cz z (ripe, to R)` of the integral over the outputs psi_k on T^(k) cap Z and the internal variables of the removed kernel `Trem(a)` (an `LFKernel` on the types of `KerBound a k`),
times e^{E_k|Z|} (absorbed in K for rem, as in III.8.7), against the factor F of the rest of the term (sup|F| <= 1 after the gas normalization). Then
`‖tau z‖ <= sum_a e^{-A2 lam^{p2} - H_k|Z|_k - 1 - logC(a)} <= e^{-A2 lam^{p2} - H_k|Z|_k}` by leaf 1, `sum_inv_logC_le_one`, and `p2Run <= A2 lam^{p2}` (0.3).

## 3. Leaves in dependency order (each <= 300 lines)
1. DONE `Balaban/LargeField/R/RRemovedFactor.lean`: `removed_kerBound_logC_of_window` (hyps: `hG : Gp = P.budgetG S k kappa^pre logC c`, `2 A2 lam^{p2}+1 <= Gp`, `C_R lam^{2d+1} <= A2 lam^{p2}`, `hwin : KerBound a k T (kappa^pre - C_R lam^{2d+1})`; concl `KerBound a k T (A2 lam^{p2} + HRun H0 beta k * cubeVol S c + 1 + logC)`), `CR_pow_le_A2_pow`.
2. `R/RRemovedLres.lean`: (III.8.4) arithmetic. Statement: constants `C_vol, C_E~, C'_E, C_nat, D_0, C_6, A_0, v_N` and `Mcrit_k^d <= (M crit_k)^d`, `crit_k <= crit-bar(lam)`; conclusion `LHS(III.8.4) <= C_R lam^{2d+1}` for `lam >= x_0`, with an explicit `C_R`. Reuse `Typing.critBar`, `LamStar.lean` polynomial bounds. Also `C_R <= A2 lam^{p2-2d-1}` for large x (adds to `LamStar`).
3. `R/RRemovedTau.lean`: `log b_k <= lamHat_k` under `RunningHyp`; `p2Run <= A2 lam^{p2}`; `H = HRun*M^d`, |Z|_k = card; `‖int T F‖ <= sup|F| * (int absW)` (toReal of the lintegral); output: `hrem` of the gas file from `KerBound`, `sum_inv_logC_le_one`.
4. `R/RRemovedShell.lean`: volume of the window variables <= 1: psi'' ball (chi''), psi_{k1} on U~3 \ Z_{k1}, multiscale shells (Lambda17'); extends `QuietBound.shell_*`.
5. `R/RRemovedKernel.lean`: Definition III.8.5: `Trem` as an `LFKernel` from the pre-kernel, `outcomeKernel` (rem weight), translation psi'' = psi~ - psi^0, division by the denominator; the pointwise exponent bound (2.58') with `Denominator`. Inputs: `GaussChange`, `DomainIdentity`, `RhoZeroPhysical`. Likely 2 files.
6. `R/RRemovedWindow.lean`: (III.8.5) at gamma = 0 for `Trem`: steps (1)-(4): Fubini order, ball/tree volumes on Z^c_0 cap Z and Z_0 (leaf 4), (D5) for the core (`locOp_pkgBound_kappa`), the exponent sum with `c_1 >= C_W`; concl `KerBound a k Trem (kappa^pre - C_R lam^{2d+1})`.
7. `R/RRemovedFinal.lean`: `lf4R_removed`: (3.10') for all ripe components, feeding `RGasCoreFinal` (replaces `hrem`).

## 4. Design check for leaf 5: the removed kernel (W879, 2026-10-17)
Source: P7 (3.6)-(3.10), pp. 518-520; LFR Def. III.8.5 (3.7'), Lemma III.8.7 (removed: `K^(3.7) chi_{Z''} e^{E_k|Z|}`, no `rho_{k,0}`), Thm III.8.9 (c).
**4.1 The operations.** P7 obtains (3.7) from `rho(A,sigma)` by: the composition (2.8)/(III.1.4) (integrate `J` and `psi_k` on `Z_0` in the composed Gaussian), Lemma III.7.1 (drop the window characteristic functions outside `U`), the translation `psi'' = psi~ - psi^0_{k1,k}`, (2.58'), division by (3.5). All but the division are identities of integrands or measure-preserving changes of variables, so the operator of (3.7) is
`K^(3.7)(psi_k, x) = chi_{Z_0} * [int dpsi_k|Z_0  K^pre chi~_k chi_S chi^0 chi''] / [int dpsi_k|Z_0  rho_{k,0}(Z)]`   (*)
on the variables of `T^pre`, and (3.7') is a theorem about (*) (Lemma III.8.7 (1)-(2); leaf 6). The removed outcome is (*) times `chi_{Z''}`, applied AFTER `R`.
| factor of (3.7) / (3.10) | Lean |
|---|---|
| `K^pre`, `b^pre`, variables `I(Z,a)` | LANDED `preOp ... (fun Y _ => locOp ...)` (`OpPkg`: `A`, `T`, `dom`, `vanish`) |
| `chi~_k`, `chi_S`, `chi^0`, `chi''`; `chi_{Z''}` | LANDED `chiTilde`, `chiS`, `chiZero`, `chiDD`; `chiZDD` (sets as arguments, `SmallFactorChi`); `delta psi` for `chiDD` only at generating-set level (`deltaPsi`) |
| weights | LANDED `ROutcome.weight _ _ _ _ toR = t s z w`, `Outcome.weight _ _ _ _ _ rem = t s z w u` |
| integral over `psi_k` on `Z_0`; denominator (3.5) | NEW `remZeroSplit` (measure-preserving `OutT = OutZ0 x OutRest`), `remDen` |
| `rho_{k,0}(Z)`, `chi_{Z_0}`, `psi^0_k`, `E~_0` | LANDED only at the `BlockField` level and only on the tube (`rhoZero`, `rhoZeroPhysical`, `chiZeroCut`, `psiZero`, `tildeE0`); action region differs (4.3.2) |
| `e^{E_k|Z|_k}` | the real number `EZ` (`E_k` real: `IsSFFamily ... Ek`) |
| translation `psi''`, composition (III.1.4), (2.58') | not part of the definition: changes of variables / identities used in leaf 6 (`cancellation_identity` landed) |
**4.2 Decisions.** (a) Carrier: `LFKernel (OutT N R a k) (SubCfg N a k P.A) (R^N) (GIdx S n M K N)`, `P` the pre-operator package: outputs `psi_k` on `V_Z` (with `Z_0`), internal variables those of `T^pre` (`J` included; III.8.8 also writes K2 in the original variables). This is the type of `KerBound a k`, so `removed_kerBound_of_window` applies to it.
(b) `removedKernel`: `K = e^{EZ} u(o) c0(o) [int_{Z_0} K^pre ROutcome.weight(t,s,z,w,toR)] / remDen r`, `b = b^pre`; `u = chi_{Z''}`, `c0 = chi_{Z_0}`, `r` the reference density, `EZ = E_k|Z|_k` (III.8.7's `K^{(rem)}`; `EZ = 0`: P7's `T'' chi_{Z''}`). Inputs other than `P` are arguments (convention of `SmallFactorChi`); no fallback branch (division by `0` is `Rop`'s own convention).
(c) R decomposition: `remDecomp r : RDecomp (outMeasure ...)`, one component (`iota = Unit`), `W = psi_k|Z_0`, `Y = psi_k|(V_Z \ Z_0)`.
(d) Characterization: `chi_{Z''}(o) Rop (remDecomp r) rho o = r(o) e^{-EZ} int K^rem f` for `rho = int K^pre w_toR f`, `f` not reading `psi_k|Z_0` (the removed part of `R` applied to the pre-operator), and `K^rem = outcomeKernel K^nor t s z w u rem` with `K^nor` the `R`-normalized pre-kernel.
**4.3 Disagreements and flags.**
1. `chi_{Z''}` reads `psi_k` on `Z_0` (`Z_0 in Z''_0`, `Zzero_cube_mem`), which `R` integrates. `outcomeKernel K^pre t s z w u rem` (Outcome.lean: "into the kernel `K^pre`"; §1 row 1) is NOT the removed outcome; it is `outcomeKernel` of the `R`-normalized kernel (`removedK_eq_outcomeKernel`). §1 row 1 holds for K1 only.
2. Reference density: landed `rhoZero`/`rhoZeroPhysical` use `effAction` = the action on all of `Omega_1(G')`, `G' = B_k(U_k)`; P7 (1.5), Def. III.8.1: `A*_k(Z; psi_k, phi_k(B_k(U_k); psi~_k))` restricted to `Z` (Q13-SHARED item 5: OPEN). With the landed density the quotient (2.58')/(3.5) keeps `e^{beta (A(Omega_1(G')) - A*_k(Z))(psi^0, phi^0)}`. Hence `r` is an argument; a faithful instance needs the restricted-support density and Lemma III.8.2 for it.
3. The landed `R` (`famDecomp`, `famDecompPhysical`, `R_normalization*`) lives on the global `BlockField` restricted to `famTubeSet` (`famRho = 0` off the tube); the operators live on `OutT` of a localized history. Not landed: the transport `OutT <-> BlockField`, the factorization of `R` over the components of `Z_sigma`. Here: the one-component `R` on `OutT`.
4. Lemma III.1.5 / III.8.4 (i) for the localized pre-operator (`b^pre`, `chi~_k, chi_S, chi^0, chi''`, `chi^dom` do not read `psi_k|Z_0`) is not landed (only `quietRest_congr`, one quiet step); premises of the identity theorems.
5. `chi''` needs `delta psi` as a `MultiField` of the history; the bridge from `deltaPsi` is not landed.

## Status (W878, 2026-10-17): leaves 2 and 3
- Leaf 3 DONE `R/RRemovedTau.lean`: `log_b_le_lamHat`, `p2Run_le_A2_lamHat_pow`, `removed_kerBound_logC_of_window` (moved into `RRemovedFactor.lean`, replacing `removed_kerBound_of_window`, whose conclusion dropped `log C(a)`), `norm_integral_le_of_kerBound`, `norm_tau_le_of_removed_kernels`, and the composed `…_halo_of_removed_factor_run_of_kernel` (kernel hypotheses in place of `hrem`; units: gas `H = H_k M^d`, card = number of cubes `c`).
- Leaf 2 DONE `R/RRemovedLres.lean`: (III.8.4) `lres_lhs_le` for any `C_R` at least an explicit constant (`Typing.CR` is not tied to Definition III.8.6, none added), `CR_le_A2_pow_of_large`, `CR_window_of_large` (`hCR` of leaf 1 for `λ ≥ max {1, C_R/A₂}`), `lres_at_scale`.

## Status (W880, 2026-10-17): leaf 4
- `R/RRemovedShell.lean`: product-set, shell and ball bounds (<= 1, per-variable radii) on `outPartMeasure` / `subMeasure`; `chiDD_norm_lt`. `R/RRemovedShellTree.lean`: Fubini along a rooted forest of output variables, `outPartMeasure_chiTilde_le` (ball 3 delta_k per block from `ChiTildeProp`). `R/RRemovedShellVol.lean`: per-block arithmetic `tree_block_factor_le`, `zero_block_factor_le` (C_vol = log(v_N max{3,C6}^N A0^N)), `volume_zeroCutoff_le` (chi_{Z0} ball), `removed_cubeVol_le` (|Z|_k <= (M crit_k)^d).
- Not tied: the change of variables psi'' = psi~ - psi^0 and the shell predicate for psi_{k1} on U~3 \ Z_{k1} (no landed predicate; leaf 5).

## Status (W879, 2026-10-17): leaf 5
- `R/RRemovedKernel.lean`: `remZeroSplit` (measure preserving), `remDecomp` (one-component `RDecomp`), `remDen`, `remNum`, `removedK`, `toRKernel`, `removedKernel` (carrier of `KerBound a k`, `b = b^pre`); `Rop_remDecomp_removed(Kernel)` (`chi_{Z''} R[rho] = r e^{-EZ} int K^rem f`), `removedK_eq_outcomeKernel`, `removedK_add_one_sub`, `removedKernel_support`, `removedKernel_vanish`. `R/RRemovedKernelPre.lean`: `removedKernel_preOp_chiDom`.
- `R/RRemovedExponent.lean`: `removedFactor_le` ((2.58') bound from `cancellation_identity` and Lemma III.6.4 (a)-(c), carrying `A_den - A_Z`, 0 in the source), `cancelBracket_add_Cnat1_ge` (`beta_k{...} + C1 >= -1/2`, real domain), `removedFactor_le_of_identity`.
- Not done: the faithful instance of `r` (§4.3 item 2), the translation `psi''` (a change of variables for leaf 6), the composition (III.1.4) for the localized quiet kernels.
