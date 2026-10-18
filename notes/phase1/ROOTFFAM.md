# ROOTFFAM (W1087, notes only): one family T over all tori for Root-F, and what the tower supplies

Read from source, nothing built. (?) marks items not traced to the end. Line numbers are from origin/main.

## 0. What Root-F fixes, in order
`logPartition_multiscale` (`Frozen/Roots/LogPartitionMultiscale.lean:46-77`): `δ`, then per `κ, c₉`: `L, M, β₀`; per `β ≥ β₀, ν, h`:
`kf`, then ONE `T : (ℓ) → ℕ → Torus d ℓ → Finset → (field) → ℂ^N`. For every `ℓ` with `M L^{kf+1} ∣ ℓ`: support, locality,
analyticity, bound `c₉ L^{-j(..)} e^{-κ|X|/(ML^j)^d}`, log identity. For every PAIR `ℓ, ℓ'` (both divisible): `T ℓ = T ℓ'` on the
images of any `A` in the quarter box (with `a ∈ A`, any `g`). So `T ℓ` is a function of `ℓ` alone, and the pair clause compares two
values of the same family; no "for this pair" choice is allowed.

## 1. Objects chosen once for all tori, and where the landed construction chooses them
| # | Object | Landed choice (file:line) | Level |
|---|---|---|---|
| 1 | `δ, L, M, β₀`, `κmin, StepTower T, δ₃, δfl, κdec` | `Inhabited/StepTowerChainStep.lean:49-50` (`∃ κmin T δ₃ δfl κdec, ∃ β₀`, all BEFORE `k, N₁, ν, β`); `exists_stepTower_collar*` | uniform (torus-free). Caveat (?): the landed chain is stated at `StepSetting 3 3 …` (`d = 3`, `L = 3`?, `N = 2`), Root-F has general `d ≥ 3, N ≥ 2` and `∃ L`; the instantiation of `d, N, L` must be checked before assembly |
| 2 | `kf` | Root-F: after `β, ν, h`, before `T`; landed: `k` is a free universal parameter of the chain (`:51`, `1 ≤ k`, `ν 3^{2(k+1)} ≤ 1`) | uniform, but `kf` is given by `ν` (arithmetic) and the number of gap/non-gap scales is `kf`. No torus |
| 3 | `Jr` (joint analytic representation), `F₁, Sol`, `I0`, `A₀` | `StepTowerChainStep.lean:51-58` (`∃ Jr` per `S`, i.e. per `N₁, k, ν, β, p₁`); CANONFAM table rows 2,4-6 | per torus, but values on the real chart are canonical (unique small solution, explicit polymer domains: CANONFAM). Off the chart: analytic continuation (identity theorem on `physV`, (?) connectedness) |
| 4 | `e = dz + c` (energy/determinant coefficient family) | `E0CoeffFamilyGCore.lean:458` (`fun θ C => dz θ C + c θ C`), chain `e` in `StepTowerChainStep.lean:122-170`, rot version `StepTowerRotChain.lean:38` (W1083) | per `N₁` (per torus), formula explicit in the core, forgotten (`∃ e B`) by the chain. Per-label two-torus agreement of the SAME `e` is the missing conjunct (CANONFAM, recommendation 1) |
| 5 | `Ycub ℓ X` (cube set of a polymer), `zr`, `xs`, cell data `Dat ℓ g`, `θ ℓ g` | hypotheses of `Polymer/TwoTorusGapTowerRootFBox.lean:100-135` (all indexed by `ℓ : ι`) | per torus, with explicit defining properties `sitesOf (Ycub ℓ X) = cellsOf[ℓ,X]`; the cube set of `X` should be a function of `X` and `K ℓ` only (?) |
| 6 | the "canonical torus" `can : Finset (Fin d → ℤ) → ι` and `Tn` | `TwoTorusGapTowerRootFBox.lean:110` (`can` quantified inside the `∀ {ι G}` block), `:195-197` (`Tnf a ℓ g X = if Q ℓ X then Tt (can X) g X else Tt ℓ g X + ∑ X₀ (Tt ℓ g X₀ - Tt (can X₀) g X₀)`); `TwoTorusGapTowerStep.lean:385` | per FINITE family `ι` (and per root cell `a`, `Tnf a` at `:185-186`); required `K ℓ ≤ K (can X)` (`:115`) |
| 7 | witnesses `c, dz, mObs` of the gap-scale step identity | `TwoTorusGapTowerCloseCore.lean` (W1021 (1)): "once per torus, functions of the side and scale data" | per torus, canonical formulas, ONE constant `B` for all tori |
| 8 | step families at scale `j` and inherited terms `Tinh` | W1021: `Tinh = 0` at the first gap scale; later scales: W1041 (3) "not covered", W1039 (3) | per scale; NOT landed for `j ≥ 2` |
| 9 | source / background `φ_k`, `θ ℓ g = (raw, σ g)` | `TwoTorusGapTowerRootFBg.lean` (W1052 (2)): `φ_k ≡ h₀` at the unit datum, source term exactly `⟨g,h₀⟩` | per torus; for general data `φ_k - h₀ ≠ 0` (below) |

Summary: (1)-(2) are already torus-free. (3)-(5), (7) are per torus but explicit/canonical. (6) is the only choice that depends on a
finite family, and it is the problem of blocker 7 / W1041 (3). `Tn` is built from tower terms `Tt` at the canonical scale `can X`; `e` does
not carry the dependence (CANONFAM, last paragraph of (2)).

## 2. Is a uniform choice available?
(a) Rows 3-5, 7: yes, "canonical per torus" suffices, because Root-F needs one `T ℓ` per `ℓ` and agreement of the SAME objects.
Missing: the agreement of `e` between tori at the level of labels (two-torus lemmas exist for the E1 part, `gsumCoeff_e1_twoTorus_*`,
`Polymer/TwoTorusE1Coef.lean:961,1063,1348`; recentred versions W1010; `dz` by the W988/W1021 chain), with the bookkeeping that all
three are produced by the same core (`towerGapTerms_twoTorus_fromTowerG_core`). This exists on ONE family of tori of all sizes (W1021 (2),
`towerGapScale_resum_fromTowerG`: "resummed on ONE family of tori of all sizes (K ≥ 2)"), so "all tori at once" is already how it is stated,
with `ι` the index type of the family. If `ι = {ℓ : M L^{kf+1} ∣ ℓ}` (infinite), `can` can only be defined by a limit.
(b) Row 6: no uniform choice landed. `can X` is the smallest torus in the family on which `X` is in the quarter box (`K ℓ ≤ K (can X)`), so
it depends on `X` and on WHICH tori belong to the family; for the infinite family `ι` the minimum exists (the family is a set of naturals,
`K (can X)` = least admissible `K`), so `can` is well-defined on an infinite `ι` as an argmin, and `Tn ℓ g X = Tt (can X) g X` for
`Q ℓ X`. Then agreement on `A` in both quarter boxes is `Tn ℓ A = Tn ℓ' A` BY DEFINITION (`:326` of `…RootFBox.lean` and `Tnf` clause
at `:200`). Problem: `Tn` needs `Tt (can X)` with `can X` the SAME torus for both `ℓ, ℓ'`, which holds for argmin over the whole family;
what W1041 (3) flagged is that the proof `K ℓ ≤ K (can X)` and the transported geometry were only given for pair families (`ι` abstract,
so ι infinite is allowed by the statement: `ι G : Type*`, no finiteness). (?) Check that no step of `Polymer/TwoTorusGapTowerStep.lean`,
`…Close*` uses finiteness of `ι` (the sum over `P ℓ` is over finsets of `ℤ^d`, not over `ι`; I found no `Fintype ι`). If so, ι = all
admissible sides works verbatim and the "finite-family dependence" is only the way the earlier notes read the statement (confirm by
instantiating `ι := {ℓ // M L^{kf+1} ∣ ℓ}`).
The ordering problem: `can X` minimises `K ℓ`, but `Q ℓ X` (X in the quarter box of `ℓ`) holds for all large `ℓ` and fails for small; the
argmin is over `{ℓ | Q ℓ X}`, nonempty because `X` is finite. OK.
(c) Quantifier order in Root-F: `T` after `β, ν, h, kf`, but `Tn` is a function of `(can, Tt)` where `Tt ℓ` uses `Dat ℓ`, `θ ℓ`; all depend only on
`ℓ` (and `β, ν, h`), so a single `choose` after `kf` produces `T`. Compatible.
(d) The inversion "build on `Z^d` and restrict" is NOT available: the tower has no infinite-volume object landed; the limit over tori
is the only route (this is the content of blocker 7's "common value is the limit over growing tori").

## 3. Two-torus agreement, term by term, against what is landed
| Term | What Root-F needs | Landed | Gap |
|---|---|---|---|
| step energy `c` (E1 part of `e`) | `c ℓ zr θ (Ycub ℓ X) = c ℓ' …` for `X` in both quarter boxes | W1010 (2) `towerEnergyCoef_twoTorus_fromTowerG` (recentred, hypothesis `L ≤ (K-26)/25+1`); W1021 `hen` | below `Kthr = 300L + 100`: no equality, only closeness `hbd` (W1021 (2)); it is made exact only by the `can` construction (6). Large-`ℓ` scales fine |
| determinant `dz` | same | W988 `towerNewTerms_twoTorus_fromTowerG` (`hdt`), formula `hEterm`, `detActivityBg_rot` | none at gap scales |
| observable `mObs` | same | W988 `hob`; W1052 (1) `mObs_rootF_of_obsBound` (explicit `Co`, Root-F shape) | none at gap scales |
| inherited terms `Tinh` | enter the step as terms of earlier scales | `Tinh = 0` at the first gap scale only (W1021 (2)); abstract induction `resum_gapScale_*` ("closeness of the inherited terms from earlier scales") | at `j ≥ 2`, `hrawO/hsrcO/hrawR` supplied by induction (W1039 (3)); and for NON-gap scales (those above where `ML^j ≪ ℓ`? the "last-scale" terms) only the `can`-limit design |
| source term `⟨g, h⟩` | `∑ g x i h i`, one site, no `X` | W1052 (2): at unit datum exactly `⟨g,h₀⟩` (`svec_bgFieldC_psiKdC_unitBg`, `fcompAtC_zeroClass_psiKdC_unitBg`); W1050 (2) `fcompAtC_zeroClass_psiKdC_eq` | for non-unit data: matching `h` with `‖h‖ = 1` is only the unit axis, so `⟨g,h₀⟩ = ⟨g,h⟩` with `h₀ = h` by rotation (`rotation covariance W1083 hTlrot`: `Q` with `Qθ ∈ physV`); (?) the rotation is by `Q ∈ O(N)`, not small — `physV` is a small neighbourhood of the axis datum, `h` arbitrary unit vector: a rotation `Q` taking `e₀ → h` is not small. Needs `hTlrot` for all `Q` (W1083: only for `θ,θ' ∈ physV`) |
| `⟨g, φ_k − h⟩`, `k ≥ 2` | decomposes into polymer terms `T_j` with bound `L^{-j e}e^{-κ|X|/..}` | W1052 (2): `φ_k = restrictφ φ_{k+1}(θ)`, only `√ν ℓ' |φ_k − h₀| ≤ K₁δ'` (`sqrt_mul_spacing_mul_vn_phiK_sub_le`) | NOT landed: a one-site function of the earlier-scale data, nonzero off the unit datum, no `L^{-je}` decay; locality in `X` and two-torus agreement need `φ_k - h` as a sum of polymer terms (the `ℳ`/`𝒫` terms of P7) |
| support `X ∌ x` etc. | `T = 0` off scale-`j` polymers of `x` | W1046 `…_supp`, `sum_cubeSets_eq_sum_polymers`; `mObs ≠ 0 → IsPolyDom` | fine-site (Finset of `Torus`) form of the sum over polymers (W1046 NOT done); `mObs` at non-corner site (cell corner only) |

## 4. Recommended construction and Lean targets
Construct `T ℓ j x X g` as follows: take `ι` = set of admissible sides, `K ℓ = ℓ/(M L^{kf+1}/…)` per tower geometry, `can X` = argmin of
`K ℓ` over `{ℓ : Q ℓ X}`; set `T ℓ j x X g := ∑_{T'} (the tower's per-site term Tn ℓ g (cell of X))` re-indexed from cells to fine sites, with the source
term and `φ_k − h` split off per polymer. Targets in order (O = needs Opus-level design):
1. (O) State Root-F's assembly with `ι` infinite: check `…RootFBox` / `…Step` / `…Close*` / `…resum_*` for hidden finiteness of `ι` and
   restate `towerGapScale_rootFSites_box_unitBg` for `ι := {ℓ // M L^{kf+1} ∣ ℓ}` (uses `Tn_eq_of_quarterBox`, `towerGapScale_rootFSites_box`).
2. (O) Per-label two-torus agreement conjunct for `e` (CANONFAM rec. 1) and spin covariance for ALL `Q` (W1083 covers `θ,θ' ∈ physV` only). Without it
   the source term for a general unit `h` is not `⟨g, h⟩`. Cost 400–700 lines (CANONFAM). Alternative with no covariance: rotate `h` into the axis by the
   lattice-free O(N) symmetry of `partitionFunction` (`Z(g;h)` with `g ↦ Qg`, exact symmetry of the model) — (?) not landed as a lemma about `T`; this
   only needs statement-level covariance of the final `T`, a cheaper route to try first.
3. Later scales (`j ≥ 2`): induction supplying `hrawO/hsrcO/hrawR` and `Tinh` from the previous scale (`towerGapScale_rootFClause`, `…_unitBg` for the base case,
   `resum_gapScale_*` for the step). (O): the inherited term is an `L^{-ge}`-decaying polymer family and must be fed back into `Tt` at the next scale.
4. Re-indexing from coarse cells (`K ℓ` cells per side) to Root-F's fine sites and polymers `X ⊆ Torus` (`four_dvd_cells_of_rootF_modulus`, `four_abs_ediv_le`,
   `isPolymer_image_cast_iff_of_quarter`, `sum_cubeSets_eq_sum_polymers`): mechanical, 150–300 lines, not (O).
5. Source part: `⟨g,h⟩` and `⟨g, φ_k − h⟩`: new lemma, a one-site contribution `g(x)·(φ_k(x) − h)` written as polymer terms; for `k = kf+1` with the unit datum
   it vanishes (W1052 (2)); for general `h` use 2. (O) for the decay `L^{-je}`.
6. Bound clause: prefactor `c₉ L^{-j(..)}` (`mObs_rootF_of_obsBound`, W1052 (1), for `mObs`; `Cdz` for `dz` DOES NOT decay (W1050 (1)); `c` similarly); the
   log identity only needs the sum identity `∑ Tn = ∑ Tt` (`:325`/`:388`). The `L^{-je}` factor for `c, dz` is a SEPARATE issue: those enter at source `0` (vacuum
   energy), cancel in `Z(g)/Z(0)` (W1042 (3)), so only `mObs` needs the factor. This is the clean reading: `T` = `∑ mObs` over cube sets of `X`.
7. Final identity: `log Z(g)/Z(0) = ⟨g,h⟩ + ∑ ∑ ∑ g·T` from the tower's step identity at `g`-dependent `θ` (`stepIdentity_zeroClass_fibre_fromTowerG_explicitCore`)
   and the analytic range `∑|g| < 1` (analyticity in `g` at `‖g‖₁ ≤ 1/2`).
