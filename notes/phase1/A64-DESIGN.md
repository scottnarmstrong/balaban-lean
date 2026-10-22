# A6-4 design: `FinalLargeFieldInput` (B3, 2026-10-21)

Blocker 5, large-field half. Route of ORCH-B (B-1′; `design_A64_notes`): P7 (4.1)–(4.14), P5 §§2–3, P6 §2 with `S_{k+1} = ∅`;
LFR Lemma IV.4.2, Theorem IV.4.1. Every claim below about the class was checked against the Lean clauses named in §3.

## 1. The objects

**1.1 The histories that remain.** By R12 (`postTerm2_of_rem`, `lastHistInt_of_rem`) and `card_remFree_empty_eq_one`,
`∫ρ = sfIntegral + Σ_{A∈𝔄⁺} lastHistInt A` (`integral_eq_sum_lastRegionWeight`, `lastRegionWeight_empty_eq_sfIntegral_of_complete`), where
`𝔄⁺` = removal-free histories with `Z_A := (A.H.step k).Z ≠ ∅`. With the whitening `ψ = h + β_k^{-1/2} L ψ̂` of B-1′,
`sfIntegral = Σ_T` (tail set `T` = blocks with some `|ψ̂_p| > p₁`; `integral_eq_sum_blocksSplit`), and `T = ∅` is `Ξ_box`
(`ctxBoxIntegralL`). So the heavy objects are the inherited components *and* the tail sets of every history, the empty one included.

**1.2 The split (route (i), corrected).** The kernels of `A` read `ψ_k` only on `V_A := ⋃_{c ∈ PostComp A k} Vblk R a_c k`: by type,
`gWeight` reads `outOf … ψk : OutT N R a k = OutConfig N (Vblk R a k)`. The boundary terms do **not** have bounded reach: `D7Bdry2Post.loc_field`
gives dependence on the whole fine set of `X`, and `bdryDoms (Ω_k) Z_A` contains every polymer of `𝒟_k(mod Ω^c_k)` meeting `Z_A` and `Z_A^c`.
So `ℬ_A` stays inside the regional integral, as in P7 (4.2) (`ℬ^{(k)}(Z_k, 𝔸_k)` is in the integrand of `∫ dψ_k Ω_{k+1}`). For every set
`Ω` of `k`-blocks disjoint from `V_A` (Fubini over `volume = volume_Ω^c ⊗ volume_Ω`, `piEquivPiSubtypeProd`; no locality of `sfFactor2` used):
```
lastHistInt A = ∫ dψ_out ∫ dμ_A(x) gWeight(ψ_out, x) · I_A(ψ_out, x),
I_A(ψ_out, x) := ∫ dψ_in exp(bdrySum A Z_A (gMulti … (ψ_out ⊔ ψ_in) x) (gFluct x)) · sfFactor2 C vc Z_Aᶜ (ψ_out ⊔ ψ_in).
```
Choice: `Ω_A` = blocks of the cubes of `Z_A^c` at cube distance `> r₀ := ⌊R_{k-1}⌋₊ + 2` from `Z_A` (so `Ω_A ∩ V_A = ∅`; P7's `Ω_{k+1} = Ω'_{k+1}`);
the collar `C_A := Z_A^c`-blocks `∖ Ω_A` is integrated on the heavy side (P7 p. 531: `T^{(k)}(Ω^c_{k+1})` becomes `∫ dψ_k Ω^c_{k+1}`).

**1.3 `𝕋′_{k+1}(Z′, 𝔸′)`** (P7 (4.9)–(4.10)), an operator package, not a number. Heavy datum on a connected set `Z′` of `k`-cubes:
`𝔸′ = (the post components c ⊆ Z′ of a history with their localized histories and labels, a tail set T′ ⊆ Ω-blocks of Z′)`;
```
𝕋′(Z′, 𝔸′)[F] := ∫ dψ_{(Z ∪ C)∩Z′} ∫ dμ_{𝔸′}(x) ∏_c (postOp A c).T.w(ψ, x_c) ∫_{|ψ̂_p| > p₁, p ∈ T′} dγ(ψ̂_{T′}) F
```
(the inherited operator `gOp` of the components composed with the tail integration and Lebesgue on the collar). Bound (IV.4.1):
`Σ_{𝔸′ ∩ Z′} |𝕋′[F]| ≤ e^{-A₂λ̂_{k₀}^{p₂} - H_k|Z′|} t^{|T′|} v_χ^{|C ∩ Z′|} sup_{χ≠0}|F|`, from `D5Bound` at `j = k` (the bound (1.26), `KerBound`, uniform in
the collar parameters), `D6Flat` (`G_k ≥ A₂λ̂_{k₀}^{p₂} + …`, `G = κ − log C − H_k|Z|`), Lemma II.5.15 with labels (`sum_inv_logC_labelled`), the
tail factor `t = |z|2^{N/2}e^{-p₁²/4}` (`norm_setIntegral_blocksSplit_le`), `v_χ` = volume of the one-block χ-shell.

**1.4 The representation** (P7 (4.11)) is an *operator* gas (Lean P10: `gasXiOp`, `HoleOperator`), not a scalar gas: the couplings read the
variables that `𝕋′` integrates (`loc_field` on `X ∩ Z′` through `gMulti`, `gFluct`). LFR Theorem IV.4.1's "the weights are scalars here, so the
operator-valued version is not needed" is not right for the class (also observed in `FinalLargeCrossing`, `FinalLargeGas`). Data:
configuration per cube = (ψ_k, all internal variables of scales `< k`, ψ̂), each with a probability reference measure (Lebesgue/Haar written as
density × Gaussian/normalized Haar, the density inside `τ`); heavy objects `z = (Z′, 𝔸′)`; couplings: (a) `ℬ″` (old `ℬ^{(k)}` re-expanded in the
regional integral, activated by the heavy objects they meet, decorated by `𝔸′ ∩ X`, `loc_hist`); (b) the Mayer links `e^{W_Y} − 1` of box terms
meeting a heavy object; (c) `e^{-a(P)} − 1` for box-gas polymers `P ⊄ Ω_Γ` (exact: `Ξ_box(Ω_Γ)/Ξ_box = exp(−Σ_{P ⊄ Ω_Γ} a(P))`, since `localGasP` is
local); (d) the normalization cycles of `det(L^{-1})_{Ω^c_Γ Ω^c_Γ}` through ≥ 2 components (all-required activation; C3's
`det_one_add_eq_exp_sum_defectTerm`). Then `∫ρ = Ξ_box · gasXiOp(…)`; KP (`gasOp_pe_hole`, generalized to weighted counts) gives
`log = Σ_Y P(Y)`; B2's regrouping (`regroupFam`) gives `LastScaleTorusClauses`; closeness is ORCH-A's.

**1.5 No vacuum term.** `FinalLargeFieldInput` has none: the per-torus constant `log(∫ρ(0)/Ξ_box(0)) − Σ_X a_T(X; 0)` goes into
`b(ℓ, k+1, ∅, ·)` (`∅` is not `IsPolymer`; every clause of `ObservableActivitiesAt` reads increments only).

## 2. The statement and its sub-Props
```
theorem finalLargeFieldInput_of_gasForm (hG : FinalLFGasForm d N δ T P6 C7 PB cs₀ M1 c rH ϱ cut) :
    FinalLargeFieldInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ cut            -- assembly (A2 + 1.5)
theorem finalLFGasForm_of_parts (hPre : PrefixInput …) (hT : LastStepTies …) (hD : CutSfDomInput …)
    (hH7 : LFH7SupportInput …) (hR : FinalLFRegionalInput … cut) : FinalLFGasForm … cut
```
| sub-Prop | content | source | size | inhabitation |
|---|---|---|---|---|
| `FinalLFGasForm` | per member, `∃ aT E κ' B a λ t₀` with A2's numerics, `LastScaleTorusClauses aT ∧ LastScaleTwoTorusClose aT ∧ ∫ρ = Ξ_box e^{E + Σ aT}` | LFR Thm IV.4.1 | — | exemption of the seven inputs; clause preds by `lastScale…_zero` |
| `LastStepTies` | row 13 `H₀ ≥ 2L^d(C′_E+1)` (per-block Gaussian normalization `≈ (N/2) log β_k`, vacuum), (Λ31) `h ≥ B_cpl e^{B_cpl}e^{κ′c}K′₀+…`, `p = p₀` (tail, `tail_exponent_run`) | LFR row 13, (Λ31); P7 (4.12) | 100 | numbers: witness `H₀` large |
| `CutSfDomInput` | on `{χ_Y ≠ 0}`, `Y = Z^c`, the composed fields of `bg(𝔹_k(W₂ Y))` lie in the term domains: `sfFactor2 C vc Y` Borel, bounded | A4-1i for cuts (W1151s) | 600 | zero at `A₀ ≤ 0` |
| `LFH7SupportInput` | kernel ≠ 0 ∧ `χ_{Z^c}` ≠ 0 ⇒ `(gMulti, gFluct, g) ∈ H7Domain(X)` for every boundary domain (so `D7Bdry2Post.bound` applies) | P5 (1.36)–(1.37), II.3.5 | 400 | vacuous at the empty-history witness |
| `FinalLFRegionalInput` | `∃` torus local form (`BoxLocalForm`) and regional local forms `LFRegionalForm A` for `A ∈ 𝔄⁺` (centre `ψ_loc` of the massive problem, whitening, `W^A, U^A`, normalization) with exact far agreement and `loc_hist` (§4), **and** `LastScaleTwoTorusClose` of the activities `lfAct` defined from these data (the conjunct is ORCH-A's; a separate "for all data" closeness would be false) | P7 (4.2)–(4.9), P5 (2.16)–(2.48), (3.1)–(3.18); P6 p. 3, (D8), `LFCoherent` | 3,500 + ORCH-A | zero datum where `I_A ≡ 0` (`A₀ ≤ 0`); `lastScaleTwoTorusClose_zero` |

Proved inside (B3): the split 1.2, `𝕋′` and (IV.4.1) (600); history factorization (`𝔄⁺` with region `Z` ↔ `ω_k`-separated families of
component local histories; from `glue_step`, step-level core of Lemma III.10.2) (600); the operator gas with σ-finite reference measures and
weighted counts (core generalizing `gasOp_pe_hole`, `gas_activity_bound`) (800); couplings (a)–(d) and their bounds (800); KP, regrouping,
torus clauses (500); the assembly (150).

## 3. Check of the route against the class
| route item | class clause / landed | verdict |
|---|---|---|
| (i) `𝕋_A` does not read `Ω_A` | `OutT = OutConfig N (Vblk …)`, `Vcubes = nbhd 1 (thick ⌊R_{k-1}⌋ Z)` | ✓ by type |
| (i) `ℬ_A` does not read `Ω_A` | `D7Bdry2Post.loc_field` reads all of `X`; `X` unbounded | ✗ — `ℬ_A` inside `I_A` (1.2) |
| (i) `sfFactor2(Z^c)` reads `(Z^c)^≈` only | `phiK` on `W2 R Y`, `chiY` with `dirRadius`; no locality lemma | not needed for Fubini; lemma for (iv) |
| (i) integrability | (1.26) ✓; `|e^ℬ| ≤ e^{B₀Σe^{-κd}}` needs support ⊂ H7 domain; cut `sfFactor2` | `LFH7SupportInput`, `CutSfDomInput` |
| (ii) massive regional problem | `FinalHoleBackground` (Thm 7.1 on any generating set) | open: minimizer of `actStar2(Z^c)` in `ψ_in` is `Qφ_{k,0}` (P7 (4.4)), local configurations |
| (ii) regional rows = torus rows off `∂Ω` | `finalWhiten` reads `unconstrainedUnitOperator` on boxes | ✗ **O1** (§4) |
| (ii) `χ_k` local in `ψ̂` | `chiY = cubeProd` of `chiKLong(□)`; finite range `finalWhiten_eq_zero_of_not_mem` | ✓ |
| (ii) tails | `FinalTail*` (T-1–T-4, L1–L5); `p₂ < 2p` (`tail_exponent_run`) | ✓; needs `p = p₀` (`LastStepTies`) |
| (iii) box sites | `rootedExpansion_linField`, `localFormOf` (generic centre, cut family); `LocalGasFormE` | ✓ generic |
| (iv) exact completion | needs every piece computed from local data | ✗ with B-1′ (O1); fix F1 |
| (v) weights | `D5Bound` (j = k), `D6Flat`, `sum_inv_logC_labelled` | ✓ (1.3) |
| (v) `H₀` against the last Gaussian normalization, `B₀` | `TypingClauses`: `0 < H₀`, `c_v ≥ M^d(H₀+c₁+3)` only | ✗ missing tie → `LastStepTies` |
| (v) couplings | `D7Bdry2Post.bound` (`C7.B0`, `P6.κ`), `loc_hist`, `analytic` at `hSetB` | ✓ on the H7 domain |
| (v) histories ↔ compatible families | `IsComplete`, `Agree`; `glue_step` | open lemma (§2) |
| (v) operator gas | `gasOp_pe_hole` needs `IsProbabilityMeasure`, unweighted `hcount` | core generalization |
| (v) `g`-analytic, `g`-local | `LFKernel.analytic_b`, `StepData.b_supp`, `D7` `loc_field` | ✓ |

## 4. Obstruction O1 and the fix
**O1.** Route (iv) asks that the regional activities agree *exactly* with those of `Ξ_box` away from the large-field set. With B-1′ this fails.
Row `p` of `L = finalWhiten` is row `p` of `boxCut(1_{locDom p})`, i.e. of `taggedCfin`, built from `boxG U (B z) t = (U|_{B_z} + t)^{-1}`
with `U = a − a² Q (N²(−Δ) + ν + aQ*Q)^{-1} Q*` on the **whole** torus; the mismatch `U`-terms of `BoxLocalForm` use the whole-torus Hessian
`D`. For a history with `Z ≠ ∅` the regional operators (on `𝔹_k(W₂(Z^c))`) have `U^Z|_B ≠ U|_B` and `D^Z(p,q) ≠ D(p,q)`, in general at every
pair, not only near `Z` (already for `H = −Δ + m²` on the cycle `ℤ_n`: the Dirichlet Green function of `ℤ_n ∖ {0}` is
`G(x,y) − G(x,0)G(0,y)/G(0,0)` (inverse of a principal submatrix) and `G > 0` entrywise, so the two differ at every pair; the difference
decays like `e^{-r dist(·,Z)}`, `finalMass_resolvent_decay`). Hence (a) the regional
localized square root has rows different from `L`'s at every `p`; (b) if `L_{ΩΩ}` (the torus `L` restricted) is used instead, the rows agree
but the regional mismatch `L_{ΩΩ}ᵀ D^Z L_{ΩΩ} − 1` differs from the torus one at every pair by nonzero amounts that depend on *all* components
of `Z`. Such differences are not couplings of a linked gas (a coupling is a fixed function activated by the heavy objects it meets).
The same holds for any piece computed from `D`, `U` or `φ_k(univ)` rather than from local data.

**Fix F1 (local-pair principle; recommended, ORCH-B to decide as B-1″).** As reading HS-1′ of the class step (`GeneratingSet.inter`,
`HoleStep.restrict`): every piece of the last integral at a localization domain `X` — whitening row, centre, Gaussian mismatch piece, localized
term (B1's stage 1), Jacobian piece — is computed on the local pair `𝔓(X)` = the generating set and the massive final operator restricted to
`X^{+m}`. Whitening: `L(p,·)` := row `p` of the inverse square root of the final Hessian of the massive problem on `𝔓(locDom p)`; its distance
to `D^{-1/2}` comes from the massive resolvent decay (rate independent of the region; invertibility as `isUnit_finalWhiten_of_lt_one`); the
rooted expansion runs in the cut family of the local operator (`taggedGfin` is generic in `U`). Then for every `A` and every piece whose local
pair lies in `deep(Ω_A)`, the regional piece *is* the torus piece (same local pair, same data): (iv) holds exactly, and the near pieces depend
on `A` only through `A ∩ X^{+m}`. `Ξ_box` (A6-3) is the instance `Z = ∅`; its statement keeps the whitening as a parameter (B-1′), so only
B1's construction of `L`, `U` and stage 1 changes. F2 (keep B-1′, expand the non-exact differences in Möbius components over the hole set)
needs a multi-hole random-walk representation of `D^Z − D` with decay; there is no landed tool, not recommended.

## 5. Order of the Lean pieces
(A) `finalLargeFieldInput_of_gasForm` (now). (i) `Spine/FinalLFSplit.lean`: 1.1, the Fubini identity `lastHistInt_eq_regional_of_integrable`,
the integrability from (1.26) under `CutSfDomInput`, `LFH7SupportInput` (now). (i′) `Spine/FinalLFOp.lean`: `𝕋′` and (IV.4.1) (now). (v-a) history
factorization, operator-gas core (now; independent of O1). (ii)–(iv) after ORCH-B's decision on O1. Spine notes: SPINE.md item 4,
SPINE-PLAN A6-4 rows, updated with each landed piece.
