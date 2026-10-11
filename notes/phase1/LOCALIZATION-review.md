# Review of `notes/phase1/LOCALIZATION.md` (brief D-LOC-review)

Referee: independent session (Sonnet), 2026-10-11. Paper and text-layer review only; no Lean was written or run.
Sources used: LOCALIZATION.md in full; P3 text layer (`pdftotext` of `sources/BF02506385.pdf`: (2.8)-(2.17), Prop 2.1 on pp. 54-56);
D1 and P4-P7 review files; ERRATA ER-042-059; GREEN.md §3 G-3 and §4.6; LF-ARCHITECTURE.md v4 §5 (table rows 0-17 and the
quantifier prefix); SMALLFIELD.md Step 8; the landed `Balaban/Multiscale/GeneratingSet.lean` and `Balaban/Background/Contraction.lean`
(statements of `Setup`, `Nmap`, `dphi`, `prop51_core`, `Prop51Hyp`, `prop51_exists_unique`). P3 page images were not re-read; where a
point depends on the printed form of a P3 formula I say so.

## Verdict: APPROVE-WITH-CHANGES

The architecture (Option A with a one-sided Schwarz parametrix and operator-norm convergence) is sound. I rechecked the parametrix
identity, the closeness algebra (DG6), the contraction scheme (I-4a), Lemma AE, and the counting and exponent bookkeeping (GM3, GM4), and
found no error in them. I found no BLOCKER. There are four MAJOR points: the interface between the two generating sets in Lemma DL
(L-01), the exactness of the locality statements (L-02), the unverified NC3 (L-03), and the constants order against LF-ARCHITECTURE
(L-04). Each has a concrete fix. L-01 and L-02 must be settled before I-4/I-5 are frozen.

## What I checked and found correct

- **Parametrix identity (§1.3).** From `K_z = χ_z H - H χ_z` one gets `H(χ_z u) = χ_z H u - K_z u`, and `H u = H_z u = c_z f` on `supp χ_z ⊂ C_z`
  because all bonds at such a point lie in `□_z` or are Dirichlet bonds. So `H G*_1 = 1 - K_1` and `G_1 = G_D`. The convention at the Dirichlet wall is
  not even needed: `u` is zero outside `Ω_1`, so the wall bond contributes nothing to the commutator.
- **Lower bound of the partition sum at the wall.** The one-dimensional quadratic B-spline sum at a wall cube is `1/2`, so `D ≥ 2^{-d}`. This confirms the document's claim.
- **DG1 (convergence).** `‖K_s‖ ≤ c_d'(1+2d)C_χ e^{γ_w ρ_0} B_w e^{N_0κ_1}/M_1` is correct as an operator-norm estimate. Weights `|s_z| ≤ 2e^{N_0κ_1}` on the slightly larger polydisc give `‖K_s‖ ≤ 1/2`.
- **DG6 algebra.** `G_s - G_D = [(G*_s - G*_1) + G_D(K_s - K_1)](1-K_s)^{-1}`. Contributions are supported in `𝒲`, and `G_D` decays from `𝒲`. The sum over `𝒲` is uniform in the volume by Lemma 4.4.
- **Lemma AE.** The telescoping, the vanishing of non-connected terms, the Cauchy bound `B_F (R-1)^{-|C|}`, and `R-1 = e^{κ_1}-1 ≥ e^{κ_1-1}` for `κ_1 ≥ 1` are all correct.
- **GM3.** With `x = κ_2/2` and `A = (2L+1)^d (M/M_1)^d`, the layer factor is `exp[(N_n/G_0)(A e^{-x} - x)] ≤ 1` for `x ≥ max(1, log A)`. Correct.
- **GM4.** The coefficient of `|C|` is `κ_1/2 - 2κ d(2L+1)^d`. The coefficient of `Δ` is `κ - 1 - κ_0 - 2κ/L ≥ κ/3 - 1 - κ_0` for `L ≥ 3`. Correct.
- **Mode P derivation.** `N_s(0) = 0` for zero data, uniqueness in the ball, and agreement with mode U when `g = 0` are all consistent.

## Findings

### L-01 (MAJOR) The two generating sets of Lemma DL, and the layer index conventions

*Location.* §1.2 (centres `Z`, `1 ≤ m ≤ k`), §4.0 (`X_1 ⊂ Ω_{k+1}`), §4.2 (layers up to `k+1`), §4.3 (first paragraph), Def-L1/L2 (§5.1); landed `Balaban/Multiscale/GeneratingSet.lean`.

*Argument.* The landed structure `GeneratingSet d L N₀ k ϱ` has the field `top : Ω (k+1) = ∅`, layers `1..k`, and the fine torus `N₀ L^k`.
The document uses three incompatible readings.
(i) In §1.2 the centres are the cubes in `Λ_m`, `m ≤ k`. In §4.0 and I-5 the region `X_1` sits in `Ω_{k+1}`, which is empty for a landed `GeneratingSet` of depth `k`. So I-5 needs a generating set of depth `k+1`, on the torus `N₀ L^{k+1}`.
(ii) §4.2 (GM1, GM3, GM4) sums over layers `n ≤ k+1`, so `Z` and `𝔓` must contain layer-`(k+1)` cubes for the depth-`(k+1)` set. §1.2 does not.
(iii) Lemma DL uses one parameter family `s` for two different problems. The first is the background field `φ_{k+1}(s)` for `𝔹_{k+1}`. The second is the fluctuation problem `δφ(ψ',s)` for `𝔹_k`, with `φ_0 = φ_{k+1}(s)`.
The text says "the cover and cube operators `H_z` are those of §1 for the operator `H_D(𝔹_{k+1})`, with scale function `ℓ(x)` of `𝔹_k` in the cover and block terms of `𝔹_{k+1}`". This describes a hybrid operator.
The parametrix identity `H G* = 1 - K` holds only when `K_z` is the commutator of the same `H` whose cube inverses are used. For the fluctuation problem `H` must be the `𝔹_k` operator `H_D(α_0 + ξ)`, which differs from the `𝔹_{k+1}` operator exactly on the region where the layer structures differ. That region is where `X_1` sits.
So it is not shown that `G_s` for the `𝔹_k` problem uses the same cubes, the same `𝔓` and the same `s_z` as `φ_{k+1}(s)`. Without that, "F(s) is one polynomial in one set of `s_P`" (AE1, AE2) is not established. The statement "constants unchanged up to factors `L`" is not a proof.

*Fix.* State precisely, in landed terms, the pair `(𝔹_k, 𝔹_{k+1})`. Use the torus of `𝔹_{k+1}` for both, and say how `𝔹_k` is a generating set on it (depth `k`, `Ω_{k+1} = ∅`, but with the last layer equal to what `𝔹_{k+1}` calls `Λ_k ∪ Ω_{k+1}`).
Then either prove that the two covers coincide after merging the layer-`k+1` cubes with layer-`k` cubes, or define `𝔓` as the union of the parameter cubes of both problems with one `s_z` per centre of each. Add a lemma that the walk expansions for the two problems have the same `s`-locality (the (AE2) argument is termwise, see L-02). Also fix the `Z` range in §1.2.

### L-02 (MAJOR) The locality statements are not exact; they need a thickening

*Location.* DG5, I-4a(e), I-4b(iv), I-4c(v), Lemma AE (AE2), Theorem I-5 (the passage from `Y(C)` to `Y[C]`), (GM) definition of `D(P)`.

*Argument.* DG5 is correct for the Green operator (the dependence on `A` is through `A|_{□_{z_i}}`). I-4a(e) is not exact as written. In the contraction, `ξ = N_s(ξ)` at a point `y ∈ □_{z'} ∩ Y'` on the outer face of `Y(R)` uses `K δφ(y)` and `R(δφ)(y)`. These involve `φ_0` at the star of `y`, including an outside neighbour `y'` where `δφ(y') = 0` but the difference `φ_0(y) - φ_0(y')` appears in `K`. Also `F_s(y)` contains `Q^*aδΨ + b(δΨ)`, which depends on `δΨ` on the block of `y` (a block of layer `n`, side up to `L^{n+1}`). The potential `A = α_0 + ξ` on `□_{z_i}` enters `H_{z_i}`, so the walk term at a core point depends on `φ_0` and `δΨ` at distance of the order of one site (and of `φ_0`'s own range of `2L` blocks, I-4b) beyond `Y(R)`.
The claim "(thickening) is absorbed by (Cov4)" in I-4b(iv) applies to cores `C_z`, not to `□_z`. The statement "depends on data in `Y'` only" is therefore false by a margin of one site (or of `2L` blocks if `φ_0` is local through BG Lemma 5.3).
The same applies in I-5: `Y[C] = X_1 ∪ ∪D(P)`, and `D(P)` is the union of the `π'` cubes containing the `M`-cube above `P`. If `P` is at the edge of its `π'` cube, the thickening of `Y(C)` leaves `Y[C]`, and `E(X,Y)` would depend on data outside `Y`.

*Fix.* In DG5, I-4a(e), I-4b(iv), I-4c(v), AE2: replace "data on `Y'`" by "data on the `ρ_*`-neighbourhood `Y'^{+ρ_*}`" with `ρ_*` an explicit number of sites (say `2L+2`). Replace `D(P)` by the `π'`-neighbourhood of `D(P)` (the constant `(2L+1)^d` becomes `(2L+3)^d`, and (GM2)-(GM4) change only in this constant). The statement of the cover should add `ρ_* M_1 ℓ`-margins to (Cov4). This is a change of constants only.

### L-02b (MINOR) AE2 needs a comparison statement, not only a support statement

DG5 says `G_s f` vanishes outside `Y(R)` and depends on the data on a component. (AE2) compares `F(s;u)` and `F(s';u')` with `s, s'` having *different* zero sets inside `C`. The step "the dependence on `s_P` for `P ⊄ Y(C)` is nil by (DG5)" does not follow from DG5 as stated, since `Y(R_s)` and `Y(R_{s'})` are different sets.
It is true termwise: a walk term is non-zero for `s` only if all `P ∈ Q(z_i) ∩ 𝔓` have `s_P ≠ 0`, hence `P ∈ C`, and (by connectedness to `X_0`) `P ⊂ Y(C)`; so `s_{z_i} = s'_{z_i}` for all steps, and the same for `s'`. Add this as a statement (DG5') and use it in I-4a(e), whose Step 5 should be an induction on the fixed-point iterates *for the pair `(s,s')`*.

### L-03 (MAJOR) NC3 (interior pointwise bounds for the cut operator) is asserted, not shown

*Location.* §3.1 (NC3), §2.4 (ii), §7.

*Argument.* The claim "the proofs of `prop48`, `prop49` use only the equation in a ball around `x` and the `L²` decay, so they extend verbatim" is not checked. The landed pointwise files (`PointwiseCase1`, `Case2a-d`, `PointwiseGeom`, `PointwiseScale`, `PointwiseLift`, `PointwiseAgmon`, `PointwiseHolder*`) total about 3,700 lines and treat cases by the position of `x` relative to layer interfaces and to the wall `∂Ω_1`; the separation (S) is used there. For a point of `C^+` the ball is inside `□_z`, which suggests that the interior case suffices. But (S) is the only reason the landed constants are uniform at layer interfaces, and the cut operator has no wall at the cut faces (Neumann), so the "Dirichlet wall" case analysis is not what is needed. Two things must be checked: (a) that the landed local argument does not use the Dirichlet condition at a bond away from `∂Ω_1`; (b) that the weighted sum (NC3 weighted form) has a constant independent of `M_1`.
I believe NC3 is true: the source `f` near a cut face is at distance `≥ ½M_1ℓ` from `C^+`, hence contributes `e^{-γ_0 M_1/2}`, and the local sources are treated by the interior estimate. But the document should include a proof sketch (a few lines are enough: "interior estimate on a ball of radius `2L²ℓ` contained in `□_z`, Agmon for the far field"), and name the landed lemmas whose Dirichlet hypotheses must be weakened.
Boundary regularity at the Neumann face is indeed not needed: all uses are at points of `C_z ⊂ C^+` (`χ_z`, `K_z` supported there), including the Hölder part of (DG2).

*Fix.* Add the sketch; list the lemmas (by Lean name) whose statements must get a bond-subset parameter; make NC the first milestone of the Lean work and decide the fallback (reflection, GR 4.6) after the interior statement for a toy cut has been proved.

### L-04 (MAJOR) Order of constants differs from LF-ARCHITECTURE v4 §5; no upper bound on `M` found

*Location.* §5.3 and §0 (Main risk 3); LF-ARCHITECTURE table rows 4, 5, 6, 8, 10, 11, 13, 15 and the quantifier prefix.

*Argument.* In Option A the constants `K_3, K_4, B_4, B_5, c_7, δ_*` depend on `κ_1` (through `B_G e^{N_0κ_1}`), and `κ_1 ≥ 4d(2L+1)^d κ_flow`. In LF-ARCHITECTURE row 4 the "Green's function and localization constants `γ_0, K_0, …, K_5, B_5, B_6, C_3, C_4, …`" are chosen from `(d, L)` before `κ_0, κ_flow, κ_1` (row 5) and `M` (row 6), and the prefix says "outputs of G-1-G-6, P2, P3". That is incompatible with the document's §5.3(5) unless these constants move after row 5. Row 6's list of constraints on `M` (P3 (2.19), P3 p. 68, P7 (2.70)) must be replaced by `M_1 ≥ M_*(κ_1) = max(4L², c_* e^{N_0κ_1})` and (4.38).
I checked for upper bounds on `M` (the question of the brief): LF-ARCHITECTURE rows 6, 8, 10, 13, 15 contain only lower bounds or definitions after `M` (`c_9^{max}(d,γ,L,M)`, `H_0 > 2B_0K_0M^{-d}`, `c_v := M^d(H_0+c_1+3)`); the quantifier prefix says `∃m_0' ∀m ≥ m_0'`. P7's review states that the second inequality of (2.70) is "one of the strongest conditions on `M`" with "`M` large enough". P5 Thm 1 has "M, κ sufficiently large" in the order `M` before `κ`; the project order (κ before M) is forced by Root-F ("for all κ, c_9 there are L, M, β_0") and is consistent. SMALLFIELD Step 8 already lists `B_4, κ_0` after `M`. So an exponentially large `M_1` is acceptable for the constant chain; I found no constraint against it. What changes is the placement of the I-4 constants in rows 4-5 of the table. `κ_0` itself remains independent of `M` (it enters only through `K_0`, a polymer count in units of `M`-cubes).

*Fix.* Add to the document an explicit "changes to LF-ARCHITECTURE §5" paragraph: rows 4, 5, 6 as above, and one sentence that `E_0 ≥ 4C_4B_6K_0K_5` with `B_6 = N L^d B_4 + 2` is still chosen after `M` and `κ_1` (it is).

### L-05 (MINOR) The cost of multiplicative weights is misattributed; a cheaper variant exists

*Location.* §0, §2.4 (iii), N-6.

*Argument.* P3 (2.10) bounds one factor of the walk by `4dB_0 M^{-1} e^{-γ_0 d(y_i,y_{i+1})}`: only polynomial gain per step, as in the document. P3's *linear* condition `M ≥ 2(7L)^dκ_1/γ_0` comes from the geometric lemma (2.18)-(2.22): the factor `e^{κ_1}` is paid once per *new* cube of `X_ω`, and a walk that enters a new cube must travel a distance `≳ M`, which gives `e^{-γ_0 M}` from the Green decay in (2.17). So the saving is not "shared weights" as such. D1 also shares weights, `s_ω = ∏_{□⊂X_ω} s_□`, but bounds the number of cubes by the number of steps and loses the decay; hence D1's `e^{κ_1} = M^{1/2}`, with coefficient `1`, not `N_0`. The document's sentence "D1 uses the same regime" is therefore only right in kind: the exponent in the document is `N_0κ_1` with `N_0 = max_z |𝒬(z)|`, which for `d = 3`, `L = 3` is in the hundreds, against `κ_1` already of order `4d(2L+1)^dκ ≈ 4000κ`. This is harmless for existence (L-04) but should be said, and N-6 should be reworded.
*Cheap variant.* Take the parameter cubes on a sublattice of side `5M_1ℓ_m` aligned with the interaction cubes, so that each `□_z` meets at most `2^d` parameter cubes, and `N_0 ≤ 2^d`. (GM1)-(GM4) change only by the constant `(M/M_1)^d`. This is optional.

### L-06 (MINOR) R-B1 is not needed; R-B2 is needed and should list the landed changes

*Location.* §3.3 (R-B1), §3.3 (R-B2), §4.3.

*Argument.* The domain statements (i), (iv) of BG Thm 6.1 for the non-solution `ψ(𝔹_j,𝔹_k'; s)` (I-4b(v)) are not used in Lemma DL. Steps (1)-(5) use: closeness `Ψ_1(s) - Ψ_1(1)` on `X_0` (a linear formula, (2.59)); `Ψ_1(1) ∈ Ξ^c_k` by (Ξ3) at `s = 1`, where `φ_{k+1}(1)` is a genuine minimiser; (Ξ2) for the true minimiser at `Ψ_1(1) + Ψ_br`; and (Ξ3) again for the true minimiser at `Ψ̂`. So BG Thm 6.1 is only applied to genuine solutions, and R-B1 can be dropped; I-4b(v) then needs only analyticity, bounds, closeness and locality of `ψ(s)`. This removes a requirement on BG.
R-B2 is needed. The mode-U Prop 5.1 cannot serve: for the fluctuation problem `g = φ_0² - 1` has size `O(ε')`, not `≤ δ_1`, so the bound `K δ_1` and `δφ(ψ' = 0) = 0` would be lost, and (4.38) fails.
The landed code uses the Dirichlet operator in more places than the sentence "abstract Green family" suggests. In `Contraction.lean`: `Setup.green : GreenSetting G a ν` and `g_bd` (which refers to `dirichletOperator G a ν α₀`); `dphi` (defined by `(dirichletOperator G a ν (α₀+δα))⁻¹`); `dphi_eq`, `dphi_diff`, `dphi_diff_sup` (resolvent identity); `Nmap` (contains the `½H_0 g̃` term, so mode P needs a version without it); `identity52`, `isPerturbed_dphi_iff`, `perturbed_of_fixed` (they convert the fixed point into the operator equation `IsPerturbed`, which does not hold for `G_s`, `s ≠ 1`). The abstract version should stop at the fixed point (`Smap_lip`, `exists_fixed`, `prop51_core`) and keep the conversion to `IsPerturbed` as a separate step for `G = G_D`. `ContractionAnalytic.lean` (418 lines) needs the same treatment.

### L-07 (MINOR) Freeze set: freeze I-5 and V2-V5; keep I-4a-c and AE internal

*Location.* §5.2.

*Argument.* I-4a(e), I-4b(iv), I-4c(v) are stated through `Y(R)`, `Core(R)`, `𝒲`, `N_0`, `s_z`, which are implementation choices of the cover (Def-L2). Freezing them freezes the cover; this contradicts the small frozen surface (the rest should stay editable) and makes L-01/L-02 repairs cost an author approval each. Consumers (SMALLFIELD, POLYMER, P5-P7) use only the expansions of Theorem I-5 and its variations V2-V5, plus the constants `K_3, K_4, B_5` as numbers. I recommend freezing I-5 and V2-V5 only (after Def-Ξ), and leaving I-4a-c and AE as internal lemmas with the statements of the document. I-5 cannot be frozen before Def-Ξ is fixed (the document says so).
Also: Def-L4 (`dite` on the I-4a(a) statement) satisfies rule 4 only if the `∃!` theorem is proved first; that is in the plan.

### L-08 (MINOR) Answer to question 1 of the brief (Option B and the missed cheaper routes)

The decision is correct, but the stated reason in §2.2(a) is partly wrong and the decisive reason is not the one given.
(a) "The radius in `t` is `O(1)`" is not right: along `A + t 1_Z(A'-A)` the radius is `γ_1/|A'-A|_2`, which is large when the data are small. Radius is not the obstruction for the potential alone.
(b) The decisive point is the fixed analyticity margin of `E`: `E(X;·)` is analytic on `Ξ^c_j(1, ε_j)` and the arguments lie in `Ξ^c(ε')` with `ε' ≤ ε_{k+1} ≤ (1-η_ε)ε_k`, so the margin is a fixed factor `1 + O(η_ε)`, not `e^{κ_1}`. Any family obtained by scaling data (or deviations from a reference configuration) by `s` has radius `1 + O(η_ε)` in `s`. This kills the "interpolation of the data rather than of the operator" route. The reference configuration "constant extension of the boundary values" removes the jump at `∂Y` (the objection in (b) is thereby weakened) but does not give a large radius, and mixed differences `Δ_C F = Σ_{S⊂C}(-1)^{|C∖S|}F(u^S)` are bounded only by `2^{|C|} B_F` without the decay `e^{-κ_2|C|}` that (GM3), (GM4) need.
(c) Exactness (the terms are activities of disjoint polymers) is correct.
So only a family that changes the *propagation* and moves the fields on `X_0` by `≪ margin` works. That is what the walk expansion gives. I found no cheaper route. I recommend rewriting §2.2 along these lines.

### L-09 (MINOR) Errata candidates N-1 … N-8

- **N-1** (partially covered cubes at layer interfaces). Plausible for the document's cover; for P3 I cannot decide without the page image (P3's cubes `D` are the partition of [1] between (2.25) and (2.26), and P3 uses the extended layers `Λ^{(m)+}`). Keep it as "a design difference", not an erratum, unless shown.
- **N-2** (`δα_k(s) = 0` on `Y_0`). P3 Prop 2.1 (p. 55 of the text layer) states it, for finite `λ`, where `δα` is determined algebraically by the second equation, `δα = λ(φ_0·δφ + ½δφ²) - α_1`. At `λ = ∞` there is no such formula. So this is not an erratum of P3; it is a property that does not survive the limit. The dropped claim is not needed in Lemma DL or I-5, which use only dependence statements; I checked P3 pp. 55-56 and 78-79. I did not re-read P5/P6 for other uses, so question 4 stays open for a second reader. Also, the parenthetical "outside the core `δα(s)` is a local function of the data at the point itself" in I-4a(e) is inaccurate: `K δφ(y)` uses `δφ` at neighbours.
- **N-3** (preserving constraint): a design point forced by `φ_0·φ_0 ≠ 1` for `s ≠ 1`, consistent with P3 p. 55 ("for `s = 1` it becomes a solution of (3.20) [3]"). Not an erratum.
- **N-4** (R-B1): not an erratum, and not needed (L-06).
- **N-5** (`ε_k ≤ ε_j`): needed and reasonable.
- **N-6**: reword (L-05).
- **N-7** (`~2` versus `~5`): follows from the document's cover; fine, but it depends on L-02 (the margin will change to `~(5 + ρ_*)`).
- **N-8** (P6 "Proposition 4.1 [3]"): P6's bibliography maps `[3] = P3` (P6 review p. 9), and P3 has Lemma 4.1, Lemma 4.2, Prop 4.3. So the reading "Prop 4.3" is right.

### L-10 (MINOR) Size estimate

The total of 18,000-29,000 lines looks low at the bottom end, for three reasons. (i) The landed modules that NC generalises are about 9,000 lines in total (`Agmon*` 1,400; `Coercivity*` 650; `Pointwise*` and `PointwiseHolder*` 3,700 and 1,400; `XVariant*` 1,900); adding a bond-subset parameter to all of them plus analyticity is closer to 5,000-8,000 than 4,000-6,000. (ii) The landed Prop 5.1 occupies `Contraction.lean` 1,176 + `ContractionAnalytic.lean` 418 + `Calculus.lean` 608 = 2,200 lines for `G = G_D` alone; I-4a for both modes plus the weighted closeness and the locality induction is 2,500-3,500, not 1,500-2,200. (iii) Not budgeted: Def-Ξ and (Ξ1)-(Ξ4) (D-SF, but they are needed for DL), the thickening and the pair `(𝔹_k, 𝔹_{k+1})` interface of L-01, and (GM2) with the layer-interface tree geometry, which is only sketched.
I suggest 24,000-38,000 lines, with NC as the dominant risk. The pair `(NC, DL)` should be costed separately after L-01 and L-03.

### L-11 (MINOR) Consistency and notation

- The symbol `π_n` is used for cubes of side `M_1ℓ_n` (§1.1, §1.2) and for cubes of side `Mℓ_n` (§4.0, §4.2: "`□ ∈ π_n` (side `Mℓ_n`) contains `P`"). Rename the first ones (say `π^1_n`).
- Def-L1 says `m_1 ≥ 1`; the blockwise structure (cut faces at multiples of `M_1ℓ_m` must be block faces of layer `m+1`, of side `Lℓ_{m+1}`) needs `m_1 ≥ 2`, which `M_* ≥ 4L²` implies. State it.
- For `Y[C] ∈ 𝒟(𝔹_{k+1})` (union of `π'` cubes in each layer) `X_1` must itself be a union of `π'_{k+1}` cubes; §4.0 says a union of `π`-cubes, each containing a `π'_j` cube of `X`. Check against P3 (4.2).
- V4 is a single line, but P6 p. 24 (4.15) uses Prop 4.3 with `X` not in `Ω_{k+1}` and a modified generating set `(𝔹_k(W_k) ∩ …) ∪ (…)^{(k+1)}`. The modified set must satisfy cube alignment and the separation (S) at its new interfaces, and `r_0`, `r_1` must be re-derived. As written, V4/V1 are not "the same three ingredients". Keep V1/V4 as open items for I-8 (question 5 of the document).
- I-4c(v), (vi): `M_{x,s}^{-1}` (Neumann series) and `K_x(φ_0)·G_s` have a one-site range, so the locality statement has the same thickening as L-02. The analytic continuation to complex data in (iv) needs the data domain to be connected (doubt (i) of the document); alternatively define `C^{(k)1/2}(s)` by the integral and prove `C^{(k)1/2}(1)² = C^{(k)}(1)` directly for small complex data, since the spectrum of `aL^{-2}Q^*Q + Δ^{(k)}` stays in the right half-plane.

## Answers to the questions of §8 of the document

1. **(D-SF, `Ξ`, `ε_j`)** Not decided by the sources I read; the gap (E) is all that is used, and N-5 is right. Lemma DL cannot be closed before Def-Ξ.
2. **(R-B1, R-B2)** R-B1 is not needed (L-06). R-B2 is needed; the precise list of landed changes is in L-06. W20 should be told the fixed-point core (`prop51_core`, `Smap_lip`) must not depend on `dirichletOperator`, and that `Nmap` needs a mode-P version.
3. **(accept NC and the exponential `M_1`)** Accept the replacement of G-3 by NC provided L-03 is done; accept exponential `M_1`: no upper bound on `M` exists in LF-ARCHITECTURE v4 §5, P3, P5-P7 (L-04). The tables must be updated.
4. **(`δα = 0` on zero cubes)** Dropping it is safe for Lemma DL and I-5 (L-09, N-2); consumers in P5/P6 beyond what I read are not excluded.
5. **(V1)** Open; see L-11 on V4. The exponent obstruction in V1 stated in the document ((GM4) needs `κ - 1 ≥ κ_0 + 2κ`) is correct.

## Summary of required changes before freezing

1. L-01: define the pair `(𝔹_k, 𝔹_{k+1})` in landed terms; one cover, one `s`; fix the range of `Z`.
2. L-02, L-02b: thickened locality statements; `D(P)` margin; termwise comparison (DG5').
3. L-03: proof sketch of NC3 with the landed lemma names; first Lean milestone.
4. L-04: "changes to LF-ARCHITECTURE §5" paragraph.
5. L-06, L-07: drop R-B1; list R-B2 precisely; freeze I-5 and V2-V5 only.
6. L-05, L-08, L-09, L-10, L-11: wording, errata classification, size estimate, notation.
