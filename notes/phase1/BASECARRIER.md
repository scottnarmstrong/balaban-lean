# BASECARRIER: the physical base carrier `BaseSmallFieldInput` (ruling R7, W1093)

Sources: P5 (2.20) (localized background `φ^b` and fluctuation `ψ'_0`, p. 505), (2.47) p. 512 (the kernel `T'^{(k)}`);
P6 (3.2) p. 16; LF-RECONSTRUCTION Def. II.7.1, II.7.6, (II.7.4); W1009 handoff ("Exact carrier change"); `BaseFirstPhysicalConditional.lean`
(`baseRho1_eq_conditional_recordInterior`). Lean: `LargeField/Base/BaseSmallField.lean`, `BaseCarrierData.lean`. **Status: defined and corrected after the source audit (BASECARRIER-AUDIT.md, D1-D3, D5, D6 resolved by W1101), NOT populated.**

**Datum (M = K = 1, a := H.localHistory 1 1 1 Z').** `Kphys H hH Z' g w o x hv : ℂ` for an admissible history `H`, a component `Z'`
of `Z^pre_1`, source `g : Torus d (L n_1) → Fin N → ℂ`, witness `w : BaseW a 0`, output `o`, new variables `x`, field `hv`. The base record is
`H.baseRecord` (no `br`, `hbr` argument) and **no raw spin is an argument** (audit D1, D2). Value: the source kernel `K̃^w_0 e^{b_0}` of P5 (2.47),
Lemma II.7.7: after the substitution (2.20) `ψ_k = ψ^{(k)}(Ω';θ) + β_k^{-1/2}ψ'` only the ultralocal Gaussian `ψ'` on `Ω_{k+1} ∩ Ω''^c` is integrated; the
background reads `θ`, not raw spins. It reads `o` (`ψ_1`), `x` (the spins on `Z'∖Ω_1`, `ψ'_0` on `Ω∖Ω''`, other new variables), `h` and `g` on the sites of
`Z'`. The sum over interior spins/`Ω''` and the sum over raw spins of the transform relation (item T) are later steps, not part of `Kphys`.

**Fields** (each quantified over `H hH Z'` and the arguments above):
`Kphys_meas`, `Kphys_outside`, `Kphys_dom` (zero off `χ^new_0`, any `g`); `Kphys_zero_sector` (`g = 0` gives real `≥ 0`; the value is `K̃^w e^{b_0(0)}`);
`Kphys_bound` (`|K̃^w(g)| ≤ K̃^w(0) e^{‖g|_{Z'}‖_1}` on the `ℓ¹` ball and `χ^new_0`: the source term of `b_0`, as in the proof of II.7.7 (b); no typing constant, audit D3);
`Kphys_analytic`, `Kphys_real`, `Kphys_supp` (only `g` on the sites of `Z'`, `baseZsites`; audit D5), `Kphys_rot` (rotate `g, o, x, hv`), `euclid_K` (S4, two histories, `HistImage`,
`RelG`, witness-summed form; no `RelCfg`). The source reindexing `Torus d (L n_1) ≃ Torus d (1·n_1·L^1)` is `baseSiteEquiv`, `baseSourceEquiv`
(explicit, `ZMod.ringEquivCongr`), `sum_norm_baseSource` (it preserves the `ℓ¹` norm); `baseSourceNorm H Z' g` is `‖g|_{Z'}‖_1`.

**Removed by the correction (W1101).** `Kphys_ext`, `baseRawSites`, `baseKt0_ext` (no raw spins); `baseRotCfg`, `RelCfg` and the clause `RelCfg σ φ φ'` of `euclid_K`; the arguments `br hbr φ` of `Kphys`, `baseKt0`, `baseK0`, `baseKC`,
`baseWit`, `BaseStepData`, `Prop279Phys.Kphys_*`, `Prop279Conclusion` and their theorems; `baseActivityExp` and the exponent `(C_b log β_0 + C_b B_0)|X|_1` of `Kphys_bound`, `norm_baseKC_le`,
`BaseStepData.KC_bound` (replaced by `e^{‖g|_{Z'}‖_1}`; the old form follows where `C_b B_0 |X|_1 ≥ 1` and `log β_0 ≥ 0`); `b0_bound_strictly_weaker` (statement about the old exponent);
the support set `Vsites` in `Kphys_supp`, `KC_supp` (now `baseZsites`, a stronger clause since `Z' ⊆ V`).

**Obligation for population (audit D4).** The source has one `b_0` for all `w`: `Kphys^w(g) Kphys^{w'}(0) = Kphys^{w'}(g) Kphys^w(0)`. It does not follow from the fields; it is a consequence of `Kphys = K̃^w e^{b_0}`
to be proved with the construction (`Prop279Phys.Kphys_reads` is its form for varying `o`).

**Theorems, not fields.** `baseKt0 := (Kphys … 0 …).re` (source-free real factor); `baseKt0_nonneg/meas/outside/dom/rot/ext`;
`baseKphys_norm_le` (bound without the support hypothesis); `baseKphys_eq_zero_of_baseKt0_eq_zero` (zero sector gives zero for all `g`);
`baseKphys_eq_Kt0_mul_exp` (per-witness: `K̃^w(g) ≠ 0` gives `K̃^w(0) > 0` and `K̃^w(g) = K̃^w(0) exp(log(K̃^w(g)/K̃^w(0)))`);
after the witness sum `baseKC_eq_baseK0_mul_exp`; `baseK0 = gaussProd · ∑_w F^w Kt0^w`, `baseKC`, their measurability, rotation, domain, modulus
(`norm_baseKC_le`), analyticity/reality/support (`baseKC_analytic/real/supp`); `baseStepData_of_input`. Inhabited by the zero input (degenerate).

**Not available any more.** A witness-independent total analytic `b_0` (W1009 two-atom example); `baseKernel_of_input : LFKernel` (its `b` is total
and analytic, so it needs `K(g) ≠ 0` on the ball; only the factorization on the nonvanishing domain holds); `BaseStepData.S2`, `GaussStructure`
on an `LFKernel` (`GaussStructureFn`, `BaseS5Fn` replace them on the real kernel); (S4) by indexing by `a` (now `euclid_K`); `b0_bound` as `|b_0|`
(now the modulus form, which is what `e^{Re b_0}` activity estimates use).

**AUDIT ITEMS (resolved, see BASECARRIER-AUDIT.md).** (1) `Kphys_bound` as a modulus bound: true for the raw conditional integral, but the (2.20) stage map
must not add a source-dependent complex Jacobian outside `K̃^w(0)`. (2) `Kphys_supp` with `V` of `a`: the source on the raw sites outside `Z'`
belongs to other components; confirm it is not read. (3) `Kphys_dom` for every `g` (the support of the integrand is source-free).
(4) `Kphys_real` for real `g` on the ball: depends on the complex background `φ^b(g)` being real there.
(5) the `br = H.baseRecord` argument is a proof term (handoff form); `br` is determined by `H`.

**ITEM T (open obstruction): the transform relation to `baseRho1`.** The relation `ρ_1(ψ; g) = (all-good term) + ∑_{H} ∑_{raw φ} ∏_{Z'} K_0(Z')·(exterior
small-field factor)` couples components through shared raw spins and carries the exterior small-field factor `A*_1`, vacuum terms of P6 (3.2) and the
`Q,R,S` selectors; none of these exists as a Lean object (W1009: no localized background, chart reconstruction, cutoff transfer, action allocation). A
field would have to contain an undefined factor or a placeholder, forbidden by rule 4. Landed exact pieces: `baseRho1_eq_sum_firstP_conditional_recordInterior`
(every `P` term, every bare spin, full energy) and the all-good sector `P = ∅` as the empty history. It is stated here only; it becomes a theorem of the
populating task.
