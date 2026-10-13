# OBSBUDGET — birth-scale budget of observable terms

**PROVED (snapshot).** Read-only inspection of `/home/scott/Balaban` at `8a1bdf723d2e424cfea29662e2c1f7b1b1847cab` on 13 October 2026. No build or edit in that repository. Here **PROVED** means a cited declaration or the stated mathematical deduction; it does not assert the physical RG induction has been formalized.

## T1. The class clause

**PROVED.** `SmallField/Def6v2.lean:126–130` (`SFTermClauses.boundM`) says, for **every** `1 ≤ j ≤ k`, rooted `x ∈ X`, `IsPolyDom P.m₀ j X`, field datum in `Dom.dom j (Tm.gs j X)`, and `l1 g < 1`,
\[
 \operatorname{vn}(Tm.M\,j\,x\,X\,\Psi\,h\,g)
 < P.c_9\,L^{-j e_P}\exp[-P.\kappa\,\operatorname{sizeJ}(P.m_0,j,X)],
 \qquad e_P=(d-2)/2+P.\gamma-P.\alpha_1.
\]
`SmallField/Def6.lean:267–272` has the same inequality with `XiDom` in place of `Dom.dom`. `sizeJ` is `treeLenCovOne` (`Def6Terms.lean:101–102`). Thus the coefficient is indexed by its **birth scale** `j`, not the present level `k`. The displayed class bound has no explicit `β_j^{-1/2}` or `β` prefactor; `c₉` is a class constant and may be chosen separately in an induction.

**REFUTED.** `Consts.Admissible` by itself guarantees `e_P>(d-2)/2`. It requires only `0<γ<1/2` and `0<α₁<1−2γ` (`Def6.lean:60–74`), which allow `α₁≥γ`: for example `γ=α₁=1/4` meets those two ranges and gives zero gap. A positive root `δ` requires the extra choice `0<δ≤γ−α₁` (strict margin is useful in the induction). The paper's order in `FLUCTUATION.md:157–158` takes `α₁<min(1−2γ,γ/2)`, so `γ−α₁>γ/2>0`; `LF-RECONSTRUCTION.md:4801–4814` uses `γ=1/4`, `δ=1/8`, and `γ−α₁≥δ`. The proposed `CONSTS.md:30` choice `α₁=1/8` gives `e_P=5/8` in `d=3`, but sits at equality in the paper's stricter `α₁<γ/2` condition and would need a smaller `α₁` for that full parameter order.

**PROVED.** A fixed `c₉` may be chosen before the final `β₀`, as the frozen root requires. The stronger phase-1 convention `c₉=β^{-1/4}` mentioned in `FLUCTUATION.md:164` and `OBSTILT.md:4` is a separate β-dependent class choice, not an explicit factor in `boundM` and not automatically compatible with the root's quantifier order.

## T2. The new term at `j=k+1`

**PROVED.** `Inhabited/Thm31bFromTower.lean:38–39` defines
\[
 A_{p,s}(b)=\operatorname{obsPrefactor}(p,s,b)
 = (\log b)^{4p}b^{-1/2-s}+(\log b)^{2p}b^{-1}.
\]
Its conditional one-step coefficient estimate (`:122`, and the corresponding later wrappers) is `C A_{p,s}(β 3^k) exp[-(3κdec/2)dExt(T')]`. The full joint family theorem `ObsFamilyJoint.lean:46ff` gives a `B₁+B₂` coefficient bound; identifying **that same family** with a uniform `C A_{p,s}` bound is a further assembly obligation. `obsFamilyRate_eq_tower` gives rate `3κdec/2`, and on active cube sets `RootActiveSize.isPolyDom_and_dExt_eq_sizeJ` identifies `dExt(T')` with `sizeJ` of its site set (`ROOTBOUND.md:19`).

**PROVED (scalar comparison).** Let `d>2`, `L>1`, `p∈ℕ`, `s>0`, and `e>0`. A bound `A_{p,s}(β L^{k(d−2)}) ≤ C L^{-(k+1)e}` uniformly in `k≥0, β≥β₀≥1` follows if
\[
 e<(d-2)(1/2+s)\quad\text{and}\quad e<d-2.
\]
The inequalities are strict when `p>0` because the logarithms require power slack. For `e=(d−2)/2+δ'`, they read `δ'<s(d−2)` and `δ'<(d−2)/2`; under the tower's `0<s<1/2`, the first implies the second. With `e=e_P`, this requires `γ−α₁<s(d−2)` in addition to `γ>α₁`. At `d=L=3`, the proposed `γ=1/4, α₁=1/8, s=5/16` meets it. The shift from `k` to birth index `k+1` costs the fixed factor `L^e`; it does not change the exponent.

**OPEN (small worker lemma, ≤150 lines).** Prove `obsPrefactor_le_scale`: for `d>2`, `p∈ℕ`, `s>0`, and `0<δ'<min(s,1/2)(d−2)`, there exists `C≥0` such that for every `b≥1`,
\[
 A_{p,s}(b)\le C b^{-1/2-δ'/(d−2)}.
\]
Use `(log b)^{4p}≤C₁ b^{s−δ'/(d−2)}` and `(log b)^{2p}≤C₂ b^{1/2−δ'/(d−2)}`. A second ≤100-line corollary substitutes `b=β L^{k(d−2)}` and yields `A_{p,s}(b)≤C β^{-e/(d−2)}L^{-ke}≤C L^e L^{-(k+1)e}`. For a prescribed fixed class `c₉>0` and fixed geometric/rate constants, increase `β₀` to absorb `C β^{-e/(d−2)}L^e` into the class budget. If `c₉=β^{-1/4}` is instead required, retain the β power and check `e/(d−2)>1/4`.

**REFUTED.** `obsPrefactor_small_scale` already proves this birth-scale estimate. Its exact conclusion (`Thm31bFromTower.lean:386–389`) is: for `0<s` and each `ε>0`, `∃β₁≥1, ∀k β, β₁≤β → A_{p,s}(β 3^k)≤ε`. The right side has no `3^{-(k+1)e}` and therefore gives only uniform smallness.

**OPEN.** To turn the scalar comparison into class H7 for the physical new term, prove the sharp prefactor for the **same** jointly analytic/local coefficient family, the root/site support and `dExt=sizeJ` identification on its supports, the datum/source-domain inclusion, and `P.κ≤3κdec/2` after any localization loss. `OBSTILT.md:§4`, `ROOTASM.md:T1–T3`, and `ROOTBOUND.md:T3` record these joins. The fixed one-step theorem is at `d=L=3,N=2` and has `k≥1, 3∣N₁, 5<N₁`; it does not cover the base step or every root torus.

## T3. Later renormalization

**PROVED.** `Fluctuation/RenormExpInputOn.lean:102–104` makes `expOldM` an expansion of the **sum of old-term differences**, with one constant `BoldM` and zero value at `ξ=0`. `thm31h_on` (`:227–241`) bounds the combined new observable by
\[
 B_{M0}+K_{loc}c_Kc_{K2}(d,L,N)B\,\varepsilon_R
       +B_{oldM}\varepsilon_R/r_0.
\]
This interface has no birth index `j`, no `L^{-je_P}` field, and no per-`j` multiplicative `1+O(ε_k)` claim.

**REFUTED.** The additive budget in `thm31h_on` implies that a retained old `ℳ^{(j)}` loses its birth-scale factor at the next step. The source construction puts these differences into **new** `ℳ^{(k+1)}`: equation (3.11) and proof (h) in `FLUCTUATION.md:620–640` sum the Cauchy-estimated old differences over `j≤k` (dominated by `j=k`) and pay them in the fresh `j=k+1` H7 budget. P4 (1.8) as recorded in `LF-RECONSTRUCTION.md:4791–4794` says the old localized coefficients are not changed after creation. The source scheme needs no product of multiplicative losses on each old coefficient.

**OPEN.** A Lean flow theorem must implement that decomposition exactly: retain each old `Tm.M j` with physical-site and torus transport, identify `oldM` as the re-expression **difference**, charge its aggregate additive cost to the new `j=k+1` coefficient, and prove the new H7 inequality. `RenormExpInputOn` alone supplies neither retained-coefficient identity nor scale-sensitive `BoldM`; its generic output cannot establish the induction. In the root, `T_j=ℳ^{(j)}(x,X;h,h,g)` for `1≤j≤k_f`, as `LF-RECONSTRUCTION.md:4791–4794` and `ROOTASM.md:T3` state; the final `T_{k_f+1}` additionally includes final polymer/large-field terms.

## T4. Consequence for Root-F

**PROVED (conditional arithmetic).** If the final-level class clause is established for every retained `j≤k_f`, `γ−α₁≥δ>0`, its term is identified with the physical `T_j`, and the class rate after all losses satisfies `P.κ≥c₁(d,L)κ_root`, then `G1_card` gives `|X|/(ML^j)^d≤c₁(d,L)(1+sizeJ_j(X))` with `M=L^{m₀+m₁}`. Hence `exp[-P.κ sizeJ]≤exp(P.κ)exp[-κ_root |X|/(ML^j)^d]`; choosing the class constant so `c₉^{flow}exp(P.κ)≤c₉^{root}` gives the frozen per-term bound for `j≤k_f`. This is the conversion in `ROOTBOUND.md:T2` and `ROOTASM.md:T2`, with its additive cover constant paid by `exp(P.κ)`.

**OPEN (actual root implication).** The premises just named are not all landed together: the physical class induction and old-term transport, exact `Tm.M`/root `T_j` identification, fine-site `IsPolymer` bridge, uniform torus coverage, and an output rate selectable for arbitrary root `κ` remain open. The final `j=k_f+1` also needs the final `R_n/P` terms and their separate entropy/amplitude estimate (`LF-RECONSTRUCTION.md:4794–4817`). Thus “class H7 + rate conversion proves the whole frozen per-term clause” is **REFUTED** without these extra inputs, while the conditional `j≤k_f` deduction is **PROVED**.

**PROVED / OPEN (parameters).** `Consts` already contains `γ,α₁,κ,c₉`, so the desired exponent `e_P` is determined; neither `e` nor `s` needs to be a class field. `StepTower` needs no `s` field for the elementary comparison: fix `s` with `γ−α₁<s(d−2)` before choosing `β₀` and pass it to the observable theorem. **OPEN** for the general root is a selectable **output spatial rate**, not another birth-exponent field: the pinned `κdec` of the current `StepTower` cannot yield arbitrary requested root `κ` after `G1_card` (`ROOTBOUND.md:T2–T4`). The general tower producer must expose a suitable rate floor or adjustable `κ₀/κdec`.

**OPEN (startable leaves).** (1) `obsPrefactor_le_scale` and its `β,L,k` corollary above (≤250 lines combined). (2) An abstract `class_boundM_to_root_old` rate/power conversion using `G1_card`, with explicit physical identification and rate hypotheses (≤180 lines). (3) A source-algebra lemma that the old coefficients remain indexed by `j` while the re-expression differences sum into the new term; start from equation (3.11) once the flow's common term family exists (≤300 lines). None requires a Lean build for this report.

**PROVED (confidence).** High confidence in the exact class and renormalization signatures and in the scalar exponent conditions; medium confidence in the cited paper-to-flow identification, which remains an explicitly open formalization step. No claim of a completed root proof is made.
