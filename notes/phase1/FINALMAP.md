# FINALMAP: the last integral after a positive stopping scale

**PROVED.** Read-only source audit at `/home/scott/Balaban`, commit `841b6e9d629d3dfb27e906a3a4fcf5ea8901ad55`. “NEW” marks proposed Lean declarations. The four FINAL names are obligations from `notes/phase1/FINAL.md`, not assertions that the full final step has
landed.

## 1. What is integrated and what must come out

**PROVED.** Let `k = kStop h > 0` for a `RunningHyp`, and write `v=n k`, `a` for its running weight, and `n_b=L^k`. The stopped-flow statements `kStop_spec`, `massLe_of_lt_kStop`, and `kStop_rootF_scale` respectively give `v>7/(8L²)`, the ordinary-step mass range
before `k`, and the scale inequalities required by `logPartition_multiscale`. `n_kStop_lt_one` gives `v<1` at positive stop.

**PROVED CONDITIONAL ON.** The input is the *physical* scale-`k` density `ρ_k` in the class after the preceding small-field and large-field flow: its zero-large-field term has the effective action and inherited local energy `E` and source/observable `M` terms on
the fine torus, with the H7 source domain; other sectors retain large-field components and boundary data. This is the conditional input of `notes/phase1/LF-ARCHITECTURE.md` LF-8, not an inhabitant supplied by `FinalHessian` or the KF0 files.

**PROVED.** The last operation integrates all remaining scale-`k` block-spin variables `ψ_k` on the coarse unit torus of side `m`, with original fine side `ℓ=n_b m`, and sums the already present large-field regions. There is no next-scale averaging quadratic. At
the constant saddle `h`, the real quadratic form on `Torus d m × Fin N` is `finalHessian d ℓ n_b m v a h`, whose scalar fine inverse comes from `n_b²(-Δ_ℓ)+v+aQ*Q`; its transverse part is the block-averaged `unconstrainedUnitOperator`, not `-Δ_m+v`.

**PROVED CONDITIONAL ON.** LF-8's full target is `∫ρ_k dψ_k = exp[-E_{k+1,0}|T^{(k+1)}|+F_{k+1,0}(h,g)+R^{(k+1)}(h,g)]`, with inherited and last-step source terms and the nonempty final large-field gas. To feed Root-F at `J=k+1`, localized `T_J(x,X;g)` must have
scale-`J` polymer support, dependence only on `g|_X`, analyticity for `‖g‖₁<1`, bound `c₉ L^{-J((d-2)/2+δ)} exp[-κ |X|/(ML^J)^d]` on `‖g‖₁≤1/2`, exact nonwinding torus agreement, and the identity for `log(Z(g)/Z(0))`. The frozen root still contains `sorry`.

## 2. The four named bridges against current Lean

**PROVED.** The matrix candidate and its real estimates have landed since `FINAL.md`: `finalHessian_eq_split` gives `D=aP_h+U(I-P_h)`, `finalHessian_form_ge_mass` gives `(8d+3)^{-1}v`, `finalHessian_inv` gives the inverse split, and `finalHessian_gap_of_running`
gives gap `7/[8L²(8d+3)]` at the stop. `finalMass_at_stop` supplies scalar resolvent and principal inverse-square-root decay with torus-uniform `finalGap` and `finalRate`. These are exact matrix statements.

**OPEN (`FINAL-HESSIAN-BRIDGE`).** Identify the leading quadratic form extracted from the actual zero-region final density at its physical saddle with `finalHessian`, including the P4 normalization, integration coordinates, and no next-scale averaging term; keep
inherited `E,M` terms in the interaction. The landed split and gap do not identify that form in `ρ_k`. The same bridge must connect the density's Gaussian normalization to the determinant used in the last integral.

**PROVED.** `FinalCutoff.lean` now has `xiBounds_cutoff_top`, `regIneq_cutoff_five`, `p4_cutoff_xi`, and `p4_cutoff_reg`. Under the displayed `XiBounds`, respectively `BlockClose` and `FieldClose`, full-block and mass-equality premises, they prove
`|ψ_k-h|<(5L+3)ε`; `p4_cutoff_xi` explicitly assumes `ν L^{2k}=n(kStop h)`.

**OPEN (`FINAL-CUTOFF-BRIDGE`).** Prove that every block integrated in the physical final density is covered by the tested region, that its actual characteristic supplies those `XiBounds` or `RegIneq` premises, and that the mass and top-layer identifiers are the
ones in `p4_cutoff_xi` or `p4_cutoff_reg`. The note also requires the complete-background late regime, including `k_f>k_0` when `k_f>0`; `kStop_spec` alone does not prove this coverage. The extra ordinary-step `chiK` is not the density's `chiXi`.

**PROVED.** `FinalComplexMatrix.lean` defines `WSmall` by weighted row *and* column sums and proves small complex perturbations of `finalOp` are coercive with decaying inverse and square root. `FinalComplexHessian.lean` defines `finalHessianC` for `h·h≠0`, proves
`finalHessianC_ofReal`, decay, and analyticity in constant complex `h`; `finalPert_hessC_inv_analytic` and `finalPert_hessC_sqrt_analytic` cover an analytic scalar perturbation `E(z)` under `WSmall r η (E z)` with `η<finalGap`.

**OPEN (`FINAL-COMPLEX-DOMAIN`).** Supply the *physical* final chart and prove that its Hessian is `hessC N a (finalOp+E(z)) h(z)`, with `E,h` holomorphic, `h·h≠0` on an open set containing the class H7 chart, and a uniform `WSmall r η` bound below `finalGap`. The
landed theorems are conditional matrix consumers; they do not show H7 lies in their domain. A cut-parameter family must retain those bounds for each local cut.

**OPEN (`FINAL-SF-LOCAL`).** Starting with that physical zero-large-field density, cutoff, chart and cut-local covariance/determinant, produce P7 (4.9)'s zero-region expression and localized logarithm `p_ℓ(X;g)` on connected unions of full side-`ML^J` blocks, with
`p_X` depending only on `g|_X`, analytic for `‖g‖₁<1`, bound `|p_X(g)|≤B_J exp[-κ|X|/(ML^J)^d]`, and exact equality across admissible tori on nonwinding supports. Prove a numerical `4√N B_J≤c₉L^{-J((d-2)/2+δ)}` to derive the source derivative part of Root-F.
`finalMass_at_stop` alone proves no exact support or torus lift.

**REFUTED.** The four bridges have all closed because the real Hessian and KF0 toolkit landed. The matrix and cutoff *algebra* are covered; physical Taylor identification, characteristic coverage, complex-domain inclusion, local final expansion, and nonempty-region
gas remain open.

## 3. Map from the one-scale toolkit

**PROVED.** `KF0WalkSeries`, `KF0WalkTruncation`, and `KF0WalkTorus` expand `K_v^{-1/2}` using powers of the nonnegative nearest-neighbour `kf0Adj`, with finite-range `kf0CR`, tail bounds, and exact nonwinding torus equality `kf0CR_torus_eq`. `KF0WalkOrdinary`
turns these weights into `kf0SeriesTerm`; `KF0WalkHalo` adds nearest-neighbour walk halos and block counts; its module header explicitly leaves the regrouped finite-support functions of Theorem F.1 open. None substitutes verbatim for `finalHessian` or its scalar
`finalOp`: block averaging creates an exponentially decaying, generally infinite-range Schur-complement kernel, and the spin projection has signed entries.

**PROVED CONDITIONAL ON.** A general F.1 engine can retain the coefficient/majorant combinatorics of `kf0SeriesTerm_hasSum` and `kf0WalkSeriesTerm_hasSum` if supplied an *actual* covariance expansion and a nonnegative majorant kernel with uniform weighted row sums,
finite-support approximants, tail estimates, and nonwinding agreement. Replace walk length by an abstract support/halo cost. Mere entry decay of `finalMass_sqrt_decay` gives a tail bound but not finite-support terms that agree exactly across tori; cut interpolation
or a compatible infinite-lattice construction is still NEW.

**PROVED.** `KF0KilledWalks`, `KF0DetWalks`, and `KF0HoleWalk` prove killed nearest-neighbour inverse, square root, loop-determinant and hole-crossing formulae. Their `kwOp`, `kwAdjG`, and positive walk-count arguments are bare-model specific. A positive mass gap
for `finalOp` permits a *different* cut resolvent and determinant interpolation, but no landed theorem identifies those killed-walk formulae with a restriction of the final Schur complement. The determinant of a restricted operator is not obtained by deleting terms
of the full inverse.

**PROVED.** `KF0TaylorMajorant` has finite-dimensional algebraic `Maj`, `quadCoeff`, and coefficient product/sum bounds that can be used verbatim for local analytic functions after choosing their variables and radius. Its `chartJac` and bare bond coefficients are
specific to the `k_f=0` sphere chart. At positive `k`, the local functions are inherited class `E,M` plus the new final interaction, with a different Gaussian covariance and cutoff domain; their majorant constants must be proved from the actual class bounds.

**PROVED.** `KF0BlockSplit` gives the exact partition and iterated sphere integral for *bare* bad/good blocks (`kf0Sector_iterated`) and collar geometry. It is not the already-renormalized density's sector identity. `KF0GoodGaussian`'s `kwSqrt` uses a general
positive-definite matrix square root construction, and its determinant and Gaussian change-of-variable proof pattern is reusable; `lintegral_good_gaussian_change` itself is typed to `kwOpSub`. A scale-`k` good-region covariance and determinant normalization are
NEW.

**PROVED.** `KF0GoodChart` proves a sphere hemisphere chart and the fixed-bad-set `lintegral_goodInner_gaussian`. At positive `k`, `ψ_k` is a block-spin variable in a class density; no verbatim hemisphere chart or fixed-bad-set sector formula follows. The reusable
step is finite-dimensional Gaussian substitution once `FINAL-HESSIAN-BRIDGE`, `FINAL-CUTOFF-BRIDGE`, and the physical chart have supplied their exact integrand and domain.

**PROVED.** `KF0BoundarySquare.schur_bound` and `completed_square` are abstract matrix inequalities and apply verbatim to a positive final good-region matrix when their stated lower-form, invertibility, and source premises are proved. `boundary_schur`,
`normal_cost`, and the bare crossing-bond reserve depend on the nearest-neighbour `kwOp` and the sphere action, so a final-boundary estimate needs a new physical source and the stopped-flow class bounds.

**PROVED.** `KF0MeanShell` has abstract `coreSource_abs_le`, `coreSource_support`, `card_blocks_dist_le`, and shell counting that can be reused on the same block torus. `mean_outside_collars` specializes to `kwOp_inv` and `kwQ`; replace its decay input by
`finalMass_at_stop` or a cut final covariance and recompute the collar constants. `KF0CollarClosure.kf0Components` and `component_local` are geometric combinatorics reusable only after the final-region blocks are identified with that geometry.

**PROVED.** `KF0CollarBudget.collar_budget_core` and `sum_collar_budget` are arithmetic after their parameters are provided. `collar_budget_gap` uses bare `kwQ`, `cL`, and `freezeRadius`, so its threshold is not a final-scale theorem. A final collar budget must use
the class's `β_k`, the decay rate from `finalMass_at_stop`, its actual boundary source, and the reserve of the final large-field operator. This is an LF-lane input, not a consequence of the small-field Gaussian gap.

## 4. The final small-field proof and bounded leaves

**PROVED CONDITIONAL ON.** With a cut family `D_{k,ξ}` preserving the real gap and complex `WSmall` margins, use its inverse square root and determinant to express the zero-region Gaussian integral on a common product measure. Expand the new chart interaction and
each inherited local `E^{(j)},M^{(j)}` on the *same* open complex chart; use the class analytic and weighted bounds to obtain local F.1 coefficients. Sum connected coefficients and use `mayer_pe` or `pe_blockTorus` only after the physical activity and its numerical
smallness are proved. `FINAL-CUTOFF-BRIDGE` gives the real chart/cutoff support; `FINAL-COMPLEX-DOMAIN` gives Cauchy radii and analytic covariance for the source ball.

**PROVED CONDITIONAL ON.** Once `p_X` has the `FINAL-SF-LOCAL` properties, set `T_J^{sf}(x,X;g)_i=∫₀¹ ∂_{g_i(x)}p_X(tg)dt` for `x∈X`, zero otherwise. Coordinate Cauchy at radius `1/4` on `‖g‖₁≤1/2` gives `‖T_J^{sf}‖≤4√N B_J exp[-κ|X|/(ML^J)^d]`. This gives the
zero-region contribution only; the nonempty large-field gas and its torus lift still contribute to `T_J`.

**OPEN (NEW leaf G1; Sonnet; start now; generator-neutral; ≤180 lines).** State a finite-index nonnegative-kernel series lemma: if `B≥0`, its weighted row sums are ≤`A`, `qA<1`, and `B_R` has support within distance `R` with weighted tail `ε_R→0`, then the
geometric series and its positive fractional-power coefficient series converge absolutely; the truncated-kernel difference has row tail bounded by a geometric multiple of `ε_R`. Reuse `kf0_neumann_hasSum`, `hasSum_coeff_walkWeight`, and `tail_bound` as proof
models, with `B` replacing `kf0Adj`.

**OPEN (NEW leaf G2; strong; start now; generator-neutral; ≤260 lines).** Given an analytic local function with finite coefficient majorant `Maj`, a covariance kernel `C` with finite-support approximants `C_R` satisfying weighted row-tail and nonwinding agreement,
construct an absolutely convergent sum of finite-support terms whose total is `F(β_k^{-1/2}Cψ)` and whose block-weighted norm is bounded by the majorant evaluated at the weighted row bound. Reuse `quadCoeff_majorant`, `kf0SeriesTerm_hasSum`, and the halo-count
argument; this statement is conditional on, not a construction of, `C_R`.

**OPEN (NEW leaf G3; strong; start now; generator-neutral; ≤220 lines).** Generalize `lintegral_good_gaussian_change` from `kwOpSub` to any finite real positive-definite `K`: with `C=CFC.sqrt(K⁻¹)`, prove `C K C=1`, `det C=det K^{-1/2}>0`, and equality of the
normalized `K`-Gaussian integral with the standard product Gaussian after `v=Cψ`. The CFC square-root and determinant proof from `KF0GoodGaussian` is the model.

**OPEN (NEW leaf S1; strong; start now; generator-neutral; ≤240 lines).** At `k=kStop h>0`, define `D=finalHessian d ℓ (L^k) m (n k) a h₀` and prove its gap, inverse, and square-root decay with `finalHessian_gap_of_running`, `finalHessian_inv`, `finalMass_at_stop`,
and `finalHessianC_sqrt_decay`; state uniform constants `finalGap d L` and `finalRate d L`. This packages landed results, without identifying a physical density.

**OPEN (NEW leaf S2; strong; start now; generator-neutral; ≤280 lines).** For restrictions or cut parameters of `finalOp`, construct a cut-local resolvent, inverse square root and determinant with the same gap, a weighted tail uniform in torus size, and exact
nonwinding agreement of finite-support approximants. Prove the cut comparison using `finalMass_resolvent_decay`, `WSmall`, and resolvent identities; a cut-family existence/geometry subleaf must precede any theorem asserting those properties for the physical final
operator.

**OPEN (NEW leaf S3; Sonnet; start now; generator-neutral; ≤160 lines).** Package `p4_cutoff_xi` and `p4_cutoff_reg` with the exact stop-index mass conversion and explicit full-block premises, outputting `|ψ_k-h|<(5L+3)ε`. This is the algebraic cutoff lemma; the
physical characteristic-cover theorem is separate.

**OPEN (NEW leaf P1; strong; wait for physical stopped density; not generator-neutral; ≤270 lines).** Prove `FINAL-HESSIAN-BRIDGE`: the quadratic coefficient of the leading final action at `ψ_k=h₀` equals `finalHessian` under the selected density and normalized
block average, with inherited `E,M` left in the interaction. Prove its Gaussian determinant factor is the one used in the final integral. `finalHessian_eq_split` and S1 discharge the resulting matrix estimates.

**OPEN (NEW leaf P2; strong; wait for LF characteristic/flow lane; not generator-neutral; ≤230 lines).** Prove `FINAL-CUTOFF-BRIDGE`: for every integrated final block in the physical zero region, derive either the `XiBounds` or `BlockClose`/`FieldClose` premises of
S3 from its actual characteristic, including coverage, `k_f>k_0`, top-layer membership, and `ν L^{2k}=n k`. This turns the algebraic cutoff into the final-density chart bound.

**OPEN (NEW leaf P3; strong; after P1 and P2; not generator-neutral; ≤270 lines).** Prove `FINAL-COMPLEX-DOMAIN`: exhibit one open relative H7 chart with analytic `E(z),h(z)`, `WSmall r η (E(z))` for `η<finalGap`, `h(z)·h(z)≠0`, and equality of its physical Hessian
with `hessC N a (finalOp+E(z)) h(z)`. Then apply `finalPert_hessC_inv_analytic` and `finalPert_hessC_sqrt_analytic` uniformly to the cut family of S2.

**OPEN (NEW leaf P4; strong; after G2, G3, S2, P1–P3; not generator-neutral; ≤300 lines per subleaf).** Split `FINAL-SF-LOCAL` into exact zero-region Gaussian identity, inherited `E,M` coefficient expansion with class H7 bounds, connected activity smallness,
localized logarithm and source derivative, and nonwinding lift. Each subleaf must carry its actual generating-set support and common source domain; the final wrapper returns `p_ℓ(X;g)` with the bound and agreement stated above.

**OPEN (NEW leaf P5; strong; wait for LF lane; not generator-neutral; ≤300 lines per subleaf).** Add the physical nonempty-region final operator and Peierls estimate, final gas activity, and torus lift; combine with P4 to get the full LF-8 integral and scale-`J`
Root-F term. `pe_blockTorus` and `mayer_pe` are consumers after these inputs. The author's item 17 concerns the `k_f=0` bare base case; G1–G3 and S1–S3 can proceed independently, while a global Root-F conclusion still needs that answer or a separate physical base
proof.

**PROVED.** The immediate reuse is therefore the stopped Hessian/cutoff matrix algebra, generic majorants, abstract square completion, and geometric counting. The unresolved proof is the exact positive-scale density-to-chart-to-local-coefficient chain and its
large-field completion. No Lean build or repository edit is claimed.
