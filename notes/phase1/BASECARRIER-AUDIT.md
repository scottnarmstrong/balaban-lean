# BASECARRIER-AUDIT: independent source audit of the R7 carrier (W1100)

Audited: `BaseSmallFieldInput` (`Base/BaseSmallField.lean`), `BaseCarrierData.lean`, `BASECARRIER.md` (W1093), W1009 handoff.
Sources: P5 (2.20) p.505, (2.47) p.512; P6 (3.2) p.16; LF-RECONSTRUCTION Def. II.7.6, Lemma II.7.7 (a)(b)(e), II.7.8; BASE-KERNEL (1.1).
Method: try to refute. Verdicts: F faithful, S stronger than source, W weaker, U unclear. Lean read only; no build.

## What the source object is
P5 (2.47) `T'^{(k)}` is NOT an integral over hard spins. It integrates only the ultralocal Gaussian `ψ'` on `Ω_{k+1}∩Ω''^c`, after the
substitution (2.20) `ψ_k = ψ^{(k)}(Ω';θ) + β_k^{-1/2}ψ'`; the background reads `θ` on `R_{k+1}(Ω')`, not raw spins. In II.7.7 `K̃^w_0 ≥ 0` is
g-independent; `K_0 = Σ_w F^w K̃^w e^{b_0}` with ONE `b_0` for all `w`, depending on `ψ_1|Ω∩V`, internal variables, `(h, g|V)`. The sum over interior
spins/`Ω''` is done afterwards (II.7.9, BASE-KF0). Its variables (II.7.8): `ψ_1` on `Ω∩Z'`, spins on `Ω^c∩Z'`, `ψ'_0`.

## Verdict table
| Field | Verdict | Source / reason |
|---|---|---|
| `Kphys` (dependent type) | **U (defect D1, D2)** | see below: raw spins `φ` are an argument the source K̃ does not have, and the sites `Z'∖Ω_1` are given twice |
| `Kphys_ext` (read set `baseRawSites`) | W, U | it says only `{x∉Z'}∪{x∉Ω_1}` are read: a superset of any (H.5) read set `U~`, so true but empty far from `Z'`; it does not forbid the double read of D2 |
| `Kphys_meas` | F | II.7.7 (a), Lemma II.3.3. Measurability in `φ` is NOT claimed (needed by T) |
| `Kphys_outside` | F | II.7.7 (a) proof: only `A_c(u)` reads `ψ_1|Ω^c`; direction of the hypothesis is right (`o,o'` agree off `gaussBlocks`) |
| `Kphys_dom` (zero off `χ^new_0`, all `g`) | F | II.7.7 (a): indicator is source-free (item 3 of BASECARRIER: confirmed) |
| `Kphys_zero_sector` | F, but identification | the real kernel is `K̃^w e^{b_0(0)}`, not `K̃^w`: `b_0(0)` carries `O(log β)` normalisations (II.7.7 (b) proof), real for real arguments, so `Kphys(0)` is real and ≥ 0. True for the source integrand (Boltzmann × indicators × positive chart Jacobian). The name `K̃^w_0(0)` in the docs is wrong |
| `Kphys_bound` | **U/S (D3)** | source: `|b_0| ≤ (C_b log β + C_b)|Z'|_1` absolute; carrier: relative to `Kphys(0)` with exponent `C_b log β_0 + C_b B_0` (`B_0 ≥ 1`, weaker constant, matches c_1,c_2 row 14). The relative form follows from the absolute only with factor 2, unless `b_0(g)-b_0(0)` is just the source term (`|<g,φ>| ≤ ‖g‖_1 < 1 ≤ |Z'|_1`, as the proof of (b) says) |
| `Kphys_analytic` | W | II.7.7 (b) "analytic on the H7 domain jointly in g": carrier has the open ℓ¹ ball and `g` only. Fine, but check the H7 domain is not larger than what S0 consumers use |
| `Kphys_real` | F | II.7.7 (b); item 4 of BASECARRIER: no complex background depends on `g` in the hard-spin step (source enters as `e^{<g,φ>}` only), so trivially true; the item is a non-issue |
| `Kphys_supp` (`V = Vsites R a 1`) | F, W | II.7.7 (b) says `g|V_{Z'}`; `V` is the `R_0`-neighbourhood of `Z'`, a superset of `Z'`. Item 2 (below) |
| `Kphys_rot` | F | rotates `φ, g, o, x, h`; `x` includes spins and `ψ'_0` (`rotSub`). II.7.7 (e): sets `A_w` O(N)-invariant, `w` fixed. Nothing the source rotates is left out |
| `euclid_K` | F modulo S4 | witness-summed form is right (`BaseW a`, `BaseW a'` differ). `RelCfg` is demanded on ALL sites (stronger hypothesis, weaker clause, safe). Needs Lemma I.3.9 for the claim that nothing but `localHistory` matters (global `H` enters only through raw sites, all of `Z'^c`) |
| theorems replacing old fields (`baseKt0_*`, `baseKphys_eq_zero_of_baseKt0_eq_zero`, `baseKphys_eq_Kt0_mul_exp`, `baseKC_*`) | F as theorems | proofs are algebra from `Kphys_bound/zero_sector/dom`; sound. But they lose the source's witness-independent `b_0` (D4) |
| `baseSiteEquiv/baseSourceEquiv/sum_norm_baseSource` | F | explicit, norm-preserving, `baseSource_zero` |

## Defects and fixes
**D1 (central): the intended value is not the source object.** BASECARRIER says `Kphys` is "the conditional integral over the interior spins of
`Z'∩Ω_1` with `φ` on raw sites fixed". The source `K̃^w_0 e^{b_0}` does not integrate interior spins: on `Ω∖Ω''` the spins are the chart image of
the free variable `ψ'_0` (the Lean `x`, fluct variables on `Ω∖Ω''`), and the `Ω''` integral comes later. A function that integrates the interior
spins AND takes `x` containing `ψ'_0` for part of them is not defined by either object. Also the source K̃ reads outside `Z'` only through
`ψ_1 = o`, `h`, `g|V`; no raw spin outside `Z'` appears in II.7.7 (b). Fix (needs ruling): state the exact value in the carrier docstring and
`BASECARRIER.md` as a formula with variables (`o`, `x`, `h`, `g|V`) and the chart, and either (a) drop `φ` as an argument (source form; then T concerns
the later sum over raw spins), or (b) keep `φ` only on the sites the sum over histories needs (collar outside `Z'` within `Vsites`) and give a lemma
that integrating `φ` out recovers (a). Do not populate before one of these is written down.
**D2: duplicated variables.** `x` has the spins on `Z'∖Ω_1` (`varSet .large = Z_1∖Ω_0`, spin-valued at scale 0), and `baseRawSites` contains the
same sites (`x∈Z'`, `x∉Ω_1`). Pairs `(φ,x)` with `φ|_{Z'∖Ω_1} ≠ x|_{spins}` are in the carrier; any value there is a fallback (rule 4). Fix:
take `baseRawSites := {x | blockMap x ∉ Z'}` (spins outside `Z'` only), or add the hypothesis `φ y = spin of x at y` on `Z'∖Ω_1`.
**D3: modulus bound.** Prove the statement as: `|Kphys(g)| ≤ Kphys(0)·e^{‖g|_{Z'}‖_1}`; then `e^{‖g‖_1} ≤ e ≤ e^{C_b B_0 |X|_1}` needs
`C_b B_0 ≥ 1` and `|X|_1 ≥ 1` (`X = Z'`, nonempty union of 1-cubes: `volScale` = #sites / L^d ≥ 1); neither is a field of `OpConsts` now
(`Cb`, `B0` are bare reals). Fix: add `1 ≤ cs.Cb * cs.B0` (and `0 ≤ log β_0` or use `log β ≥ 0`) as typing data of `OpConsts`, or state the
bound with the source's absolute form; also record that the source constant is `β` not `β_0` and `C_b·1`.
**D4: witness-independent `b_0` dropped.** The source has one `b_0(g)` for all `w`. W1009's two-atom example uses witnesses that select
spin values; `BaseW a 0 = {blk,bd}^{P_1∩Z'}` selects violated conditions, so the example is not an instance. The weakening is safe but loses what
(S0) consumers use after the witness sum. Fix (a theorem, not a field): `Kphys^w(g) Kphys^{w'}(0) = Kphys^{w'}(g) Kphys^w(0)` is true for the
source object; add it when populating, as a consequence of `Kphys = K̃^w e^{b_0}`, so that `baseKC = e^{b_0} baseK0` holds without logarithms.
**D5 (item 2 and product structure).** `V ⊋ Z'` (collar). If `Kphys` contained `e^{<g,φ>}` on `V`, the product over components of `K_0` would
count the source on overlapping collars several times; the source term in `ρ_1` appears once. Fix: the source factor in `Kphys` is on `Z'`
only (state `Kphys_supp` with `Zsites`, which implies the present clause).
**D6 (item 5).** `br` with `hbr : br = H.baseRecord` is redundant; harmless, but `Kphys_ext` rewrites through `br`. Fix (optional): drop `br`, use
`H.baseRecord`.
**D7 (item 1).** The raw-spin integral has no complex Jacobian: the chart Jacobian (II.7.7 (e), `log` of it in `a_w`) is `g`-independent, so
item 1 holds if `K^w(g) = ∫ J(...)·e^{<g,φ>}` with `|e^{<g,φ>}| ≤ e^{‖g‖_1}`; it fails if the stage map makes `φ^b` depend on `g`. Item 3: confirmed.
Item 4: confirmed trivial (see `Kphys_real`).

## Item T (transform relation to `baseRho1`)
Agree it cannot be a field today (needs `A*_1`, vacuum terms (P6 (3.2), three regions, R5′), `Q,R,S` selectors, none defined). Note that D1 decides
its form: with (a) the relation is `ρ_1(ψ;g) = Σ_H ∫dφ_raw ∏_{Z'} K_0(Z')·(exterior)` only if `φ` appears; with the source form the relation is
the P5 (2.15)/(2.47) identity with `Ω''` integrals inside `K`. Needs `Kphys` measurable in `φ`, absent now.

## Recommendation
Do NOT populate yet. Resolve D1 and D2 (carrier docstring + one field change, W1093 or the orchestrator), add D3 typing constants, then populate.
