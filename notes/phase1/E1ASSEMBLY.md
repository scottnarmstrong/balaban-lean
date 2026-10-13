# E1ASSEMBLY: a zero-class `E1MarksC` record from the tower

13 October 2026. Read-only Lean snapshot: `/home/scott/Balaban` main `c36f978` (later than the requested `5e61529`). **PROVED** means a landed declaration or an elementary deduction explicitly given below; **OPEN** means a missing Lean or physical identification; **REFUTED** identifies a false shortcut. Branch `w510-mark-corr-count` has commit `897569f`; `w505-mark-corr-total-tower` has commit `0c209b8` and a later merge. Both are **drafts**, and their statements are cited as such. No new commit was found on `w512-mark-corr-sum` or `w508-common-witness-obs` at inspection. The target is the whole-torus zero class, $d=L=3$, $N=2$, $m_0=1$, and $k\ge1$.

## T1. The type to assemble and the fixed choices

**OPEN theorem skeleton.** The following is the intended *outer* Lean declaration; `I` is constructed from the fixed choices below. It retains `StepScaleData` as a premise and fixes the threshold before the scale and root. `RootIdx 3 3 N₁ T.m₁ (k+1)` is an abbreviation of the root torus in `E1MarksC` (`Fluctuation/RootPavingMap.lean:RootIdx`).

```lean
theorem e1MarksC_zeroClass_fromTower {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁],
        3 ∣ N₁ → 5 < N₁ →
        ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
        ∀ β : ℝ, β₀ ≤ β →
        ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
        StepScaleData T k hk N₁ ν β p₁ →
        ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
          ∃ I : E1MarksC (T.step k hk N₁ ν β p₁)
              (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
              ((T.step k hk N₁ ν β p₁).blockSplit 1 (by assumption)) z,
            I.𝒰 = Metric.ball (0 : ℂ) (corrU : ℝ) ∧
            I.κG = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
            CPE 3 3 I.Kc I.κH I.κ0 I.κ' *
              (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤
                K0 3 3 T.κ0
```

Here `corrU` is `Inhabited/MarkCorrBudget.lean:corrU = 17/16`; in implementation qualify its namespace or use a local `let`. The `by assumption` placeholder for the `BlockSplit` proof is the just introduced `hp : 0 < p₁`, transported by the definitional equality $S.p_1=p_1$. A final Lean file should name `S := T.step …`, `hpS : 0 < S.p₁`, and `BS := S.blockSplit 1 hpS`; no new split is to be chosen. This skeleton is a proposed declaration, **not** a landed or elaboration-checked theorem.

**PROVED type alignment.** For each fixed scale let $b=\beta3^k$, $C={\tt zeroClass}\ 3\ 3\ N_1\ T.m_1\ k\ 2\ ({\tt rhoSep}\ T.m_1)$, $S=T.{\tt step}\ k\ hk\ N_1\nu\beta p_1$, $e_0=(\langle{\tt rawOf}\ S.D',\ldots\rangle,0):{\tt physParam}\ 2\ S$, and $a=2T.\kappa_{\rm dec}-1$. Choose `q = 1` in `Inhabited/ZeroSourceActivityCommon.lean:zeroSourceActivity_common_fromTower`. Its `reads` is the **block-indexed** family `fun (_ : RootIdx 3 3 N₁ T.m₁ (k+1)) => Set.univ`; its `dom b` is `polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b))`. `StepScaleData.covers` plus `Fluctuation/HatPolyDom.lean:isDj_of_polyDom` must supply `hdomR`; this specific proof is **OPEN** as an assembly leaf. The source theorem accepts *arbitrary* finite root-indexed `reads,dom` with `hdomR`, so these arguments have exactly the required type.

The activity labels are **common to every root**: `Lb := {Y // Y ∈ I₀.𝒴} ⊕ RootUnionLb 1 reads dom`, `Lab := commonLabels (thickLabels I₀.𝒴 I₀.dom) hN (by norm_num) reads dom hdomR`, and `A u := A0 e₀ u`, where `I₀,hF,A0` are chosen once from `zeroSourceActivity_common_fromTower` **before** `intro z`. Its source theorem returns `A0` at amplitude $\varepsilon_H=2^2(2\varepsilon_U)$, rate $\kappa_H=a$, $\kappa_0=T.\kappa_0$, and entropy constant $K_c=T.{\tt marksKc'}$. `A0` is `commonAct (zeroSourceAct A 2) … reads dom`, not a fresh activity per root. Its fixed-step `hW` is exactly for `S.WoneC C`, `BS.restr`, and $e_0$.

For one root $z$ take the mark index **only** $\iota_z:=\{Y'\mid Y'\in{\tt bridgeFamily}\ 1\ {	t reads}\ {	t dom}\ z\}$, not the sum over all roots. Put `y0 Y' := commonAnchor _ reads dom z Y'`, `F0 _ := corrF0 T k β p₁`, `κG := a`, `𝒰 := ball 0 corrU`, and
$$G_{z,Y'}(u,\Phi)=\begin{cases}O_z(u,\Phi,Y'),&\|u\|<{\tt corrU},\\0,&\text{otherwise},\end{cases}$$
where $O_z$ is `markedOutDec 1 reads dom z` applied to `decMarkCorrTerm` with the **same** chosen pair families $(F_{1,b},{\rm Sol}_b)$ for all blocks; set its clamp radius $\rho=p_1$, $cc=b^{-1/2}$, mask `Zm := S.blockU z`, and raw datum `rawOf S.D'`. The local first-mark variable is $u$; the auxiliary derivative variable inside `decMarkCorrTerm` is $t$. `Fluctuation/MarkedCommonLabels.lean:commonAnchor_marks_fields`, `commonAnchor_bridge`, and `commonAnchor_dl` show the anchor and size types match this choice. **REFUTED:** choose $\iota$ to be all root-label pairs inside each *single-root* record; that would sum marks belonging to other roots in `InterpMarks.hF`.

**OPEN nonempty-index point.** `InterpMarks.nonempty` requires `Nonempty ι_z`; neither `zeroSourceActivity_common_fromTower` nor the generic definition of `bridgeFamily` proves this for the physical `polyDom`. `MarkedCommonLabels.lean:markedCommonLabels_nonempty` constructs a separate artificial nonempty family and cannot be substituted for these `I₀,dom`. Prove nonemptiness of this physical bridge family (likely from a domain meeting `fineBlock z` in `D.covers`), or add a zero dummy mark and a **real** common label with a separately budgeted positive `F0`. The dummy option requires an actual label inhabitant and changes the budget; it must be proved, not assumed.

## T2. Every `InterpMarks` field, in declaration order

The field list is copied from `Fluctuation/Thm31cde.lean:InterpMarks` (lines 81–119). The entries marked “OPEN” describe proof terms still to be written; the listed supplier declarations themselves are landed unless marked draft.

| Field | Exact inhabitant and supplier |
|---|---|
| `Lb`, `[fin]`, `Lab` | `Lb` and `Lab` above; `Fintype` by sums/subtypes. The `A0` output of `zeroSourceActivity_common_fromTower` fixes `commonLabels … reads dom hdomR`. **OPEN** `hdomR` specialization. |
| `ι`, `[finι]`, `nonempty` | `ι_z` above; finite by `Finset` subtype. **OPEN** physical bridge-family nonemptiness or a proved dummy extension. |
| `εH`, `κH`, `κG`, `κ0`, `κ'`, `Kc` | Respectively $2^2(2\varepsilon_U)$, $a$, $a$, $T.\kappa_0$, $T.\kappa'$, `T.marksKc'` from the chosen `A0`; `κG` is the mark choice. |
| `F0`, `hN` | Constant function `fun _ => corrF0 T k β p₁`; `hN : 3^1 ∣ N₁` by `simpa` from `h3N : 3 ∣ N₁`. |
| `𝒰`, `isOpen`, `seg` | `ball 0 corrU`; `Metric.isOpen_ball`; $0\le s\le1$ implies $\|(s:\mathbb C)\|\le1<17/16$. Activity holomorphy on `ball 0 2` restricts to this disc. |
| `A` | `fun u => A0 e₀ u` from the **same** `zeroSourceActivity_common_fromTower` witness. |
| `y0`, `G` | `commonAnchor _ reads dom z`, and the clamped $O_z$ above. **OPEN** W510/W512 shared-pair specialization and nonempty handling. |
| `meas` | For each fixed $u$, if $\|u\|<U$, finite sums of continuous/measurable `decMarkCorr` from `DecMarkCorrected.lean:decMarkCorr_fields_of_pair`; otherwise `measurable_const`. `markedOutDec` reduces to finite sums using draft W510 `deriv_decMarkCorrTerm`. **OPEN** wrapper. |
| `dep` | `decMarkCorr_fields_of_pair` on each $Y\subseteq Y'$ and the cell-union bridge, then finite sums and `commonAnchor_marks_fields`. For $\|u\|\ge U$ use constant-zero dependence. **OPEN** wrapper; it must hold for every block configuration. |
| `bound` | Draft W510 `corrected_markedOutDec_count` gives $\|O_z(u,\Phi,Y')\|\le{\tt corrF0}\,e^{-a\,{\tt treeLenCovOne}\,1\,(k+1)\,Y'}$ for $\|u\|\le U$ after `MarkCorrBudget.lean:corrF0`/`Estar_eq`; `commonAnchor_marks_fields` transports this to `Lab.dl`. Outside the cutoff use $0\le F_0e^{-a d}$. **OPEN** tower specialization. |
| `holA` | `zeroSourceActivity_common_fromTower` gives differentiability of `u ↦ (A0 e₀ u).H y Φ` on `ball 0 2`; restrict to `𝒰`. **PROVED** supplier. |
| `holG` | `decMarkCorr_fields_of_pair` gives `AnalyticOnNhd` in $(e,u)$ for each term on `physV × ball 0 U`; restrict at $e=e_0$, differentiate finite sums, and use that the cutoff is identically the first branch on open `𝒰`. **OPEN** finite-sum/derivative wrapper. |
| `hκ0`, `hKc`, `hεpos` | `T.marks_hκ0`, `T.marks_hKc`, and the positive-amplitude conjunct returned with `A0`. |
| `hF0` | New `corrF0_pos T hk hβ hp`, by `MarkCorrBudget.lean:corrR_pos`, `corrU_pos`, `MarkBudgetAudit.lean:Kmark_pos`, `Estar_eq`/`Ecst_pos`, and $\beta>0$. `corrF0_le` alone does **not** prove positivity. **OPEN** small Lean lemma. |
| `hκ'`, `hκG`, `hκ` | `T.marks_hκ'`, `T.marks_hκG` (reflexive at $κ_G=κ_H=a$), and `T.marks_hκ` in `Inhabited/MarksNumericsFromTower.lean`. |
| `hε` | The returned inequality $\varepsilon_H\le {\tt stepTheta}\ 3\ 3\ T.{\tt marksKc'}\ a\ T.\kappa_0\ T.\kappa'$; unfold `Inhabited/StepOutputConsts.lean:stepTheta` to get exactly the record denominator. |
| `hW` | Fixed-step conjunct of `zeroSourceActivity_common_fromTower` at $e_0$, $q=1$, with the same `BS = S.blockSplit 1 hpS` and `A0`. |
| `hF` | Draft W512 physical sum for the **same** $(F_{1,b},{\rm Sol}_b)$, combined with draft W505 `mark_eq_deriv_blockEnergy_fromTower`/`fderiv_mask_corrected_total_fromTower`, draft W510 finite output-sum identity, `HatLabelsTerms.lean:StepSetting.ae_hatOf_restr` at $\rho=p_1$, and `ae_norm_nuFl`. On $s\in[0,1]$ the cutoff is inactive. **OPEN** until W512 and its tower specialization land. |

**Mismatch ledger.** The activity `I₀` is `DirectTerms S 1 hpS … p₁ 2 …` and uses `BS=S.blockSplit 1 hpS`; the corrected mark uses the *same* `S`, $m_0=1$, `hpS`, and `hatOf 1 p₁ hpS`. The activity's source-radius parameter is the separate $q=1$, while its direct-term hat radius is $p_1$; confusing these two radii breaks `ae_hatOf_restr`. W505 works at the tower step and a possible `withDatum D'`; specialize $D'=S.D'$ and the reflexive `hDh`, or transport **all** activity, mark, and `BS` data together to the same step. Both lanes use $Z_z=S.{\tt blockU}\ z$ and `rawOf S.D'`. A per-root choice of a new `DirectTerms` or a new pair family inside W512 would not yield the displayed `hW`/`hF` on one record. The common activity label type is `({Y // Y∈I₀.𝒴}) ⊕ RootUnionLb …`, while $\iota_z$ is only a bridge subtype; `commonAnchor` is the explicit map between them. W508's source-witness family is needed for a later jointly analytic datum/source theorem, **not** for this fixed-step `InterpMarks.hW`.

## T3. The numerical budget and one threshold

**PROVED arithmetic conditional on OPEN `corrF0_pos` and W510.** Put $K_{0c}:={\tt K0}\ 3\ 3\ T.\kappa_0>0$ (`T.marks_K0_pos`), $P:={\tt CPE}\ 3\ 3\ T.{\tt marksKc'}\ a\ T.\kappa_0\ T.\kappa'$, and $\epsilon_B:=1/(P+1)>0$. `Polymer/MarkedCubes.lean:CPE` is a formula in tower constants only, and `Fluctuation/SizeModEntropy.lean:K0` is likewise independent of $\beta,k,N_1,z$; $P\ge0$ by the formula, `T.marks_Kc'_pos`, and positivity of `c1`. Apply `MarkCorrBudget.lean:exists_beta0_corrF0_le T (by positivity : 0<ε_B) hA p`. It gives $F_0^{\rm corr}\le\epsilon_B$ uniformly in $k,\beta,p_1$. `MarkedRootGeometry.lean:bridgeFamily_entropy` at rate $T.\kappa_0$ gives
$$\sum_{i:\iota_z}I.F_0(i)e^{-T.\kappa_0 I.Lab.d_l(I.y_0i)}\le F_0^{\rm corr}K_{0c},\qquad P\sum_i\cdots\le P\epsilon_B K_{0c}\le K_{0c}.$$
The draft W510 weighted **norm** sum at rate $a''=T.\kappa_0$ has `K0 3 3 (a-T.κ0)`; it is not the record's constant-$F_0$ sum and must not be used as a substitute. `hF0` needs strict positivity as noted above. `hκG` is `T.marks_hκG`; `hκ` is `T.marks_hκ`; `hε` is the activity's returned `stepTheta` inequality. No extra $\beta$ threshold is needed for these rate fields.

Take $\beta_0=\max(3,\beta_{\rm activity},\beta_R,\beta_F)$, where $\beta_{\rm activity}$ comes from `zeroSourceActivity_common_fromTower`, $\beta_R$ from `MarkCorrBudget.lean:exists_beta0_corrR T hA p`, and $\beta_F$ from `exists_beta0_corrF0_le` with $\epsilon_B$ above. `corrR_pos` and `two_corrR_mul_decMR_lt` yield the Cauchy domain; $2U\le R$ follows from $\beta_R$. W505's committed draft has no separate asymptotic threshold once `StepScaleData` is given; W512 may reveal another threshold and would then contribute one more `max`. **REFUTED:** making `CPE` or `K0c` depend on $\beta$ to close the inequality; their fixed tower values are what make the threshold argument valid.

## T4. Regularity of the clamped bridge sum

**PROVED input, OPEN finite assembly.** `DecMarkCorrected.lean:decMarkCorr_fields_of_pair` supplies continuous and measurable dependence on every block configuration and `AnalyticOnNhd` in $(e,u)$ for each corrected $b,Y$ term. The *same-pair* theorem `DecMarkOfPair.lean:decMarkPair_family` retains the pair, its eight clauses and joint analyticity, so no new existential pair may be chosen between locality and the physical sum. The W510 draft supplies `decMarkCorrTerm` and `deriv_decMarkCorrTerm`; after reducing `markedOutDec`, $O_z$ is a finite sum over the fibre of `markedIdx` and hence inherits fixed-$u$ measurability, block dependence, and holomorphy on `ball 0 U`. A direct finite-sum lemma should be stated for the rooted output and used by every `G` field. The cutoff is a `dite` on the scalar proposition $\|u\|<U$; for fixed $u$ it preserves measurability and dependence in $\Phi$. `InterpMarks.holG` tests only $u\in\mathcal U$, so it sees the analytic first branch and asks for no boundary holomorphy. The stronger `ParamMarkFamily.holG` and `contG` can later use the same first branch on `physV × 𝒰`; they are **not** fields of `InterpMarks`.

## T5. Consumers and the actual scope of clause (a)

**PROVED conditional on the OPEN mark record.** Given $I_z$ and its budget, call `Fluctuation/StepComplexThm31.lean:e1locC_expansion_of_input I_z`. Its conclusion has $S.E1locC\ C\ z=\sum_T E_1(T)$ and a coefficient bound initially with `CPE * ∑F0 e^{-κ0 dl}`; the budget turns this into $K_{0c}e^{-T.\kappa' dExt(T)}$. The landed `Inhabited/StepTowerScale.lean:detExpansionLocC_scale_fromTower T k hk N₁ h3N hN hν0 hν β p₁` returns, for every $z$, `Dloc : DetExpansionLocC S 1 z T.t κdet cdet` and $T.\kappa'\le κdet$, where
$$κ_{\rm det}={T.\kappa-\log2-2\log({\tt detDeg}\ 3\ 3+1)\over18},\qquad c_{\rm det}={27\,{\tt covBLogMax}\ 3\ 3\ T.\kappa\over1-({\tt detDeg}\ 3\ 3+1)^2(2/e^{T.\kappa})}.$$
Use **`Fluctuation/DetOutputTerms.lean:DetExpansionLocC.toDetExpansionC Dloc D.xi`** to obtain the exact `DetExpansionC S 1 z κdet cdet` binder. The lemma uses `rootTrace_one_eq_logAC` internally and forgets the stronger datum locality/anchor fields; no new determinant expansion is needed. Then call `thm31aC_of_input_const I_z hκdet (Dloc.toDetExpansionC D.xi) hmark hdet`. For the zero-class $N=2,L=3$, one may define $B_L:=c_{\rm det}/(2\cdot3^3K_{0c})$ once positivity is proved, making `hdet` equality; alternatively retain a fixed $B_L$ with a proved `hdet`. The output is
$$S.E0locC\ C\ z=\sum_T E_0(T),\qquad \|E_0(T)\|\le(2\cdot3^3B_L+1)K_{0c}e^{-T.\kappa'dExt(T)}.$$

**Scope audit against `notes/phase1/FLUCTUATION.md` §3.1(a) and `notes/phase1/AUDIT-OBS.md`.** The exact consumers index $T$ over **all** finite sets of level-$1$ block cubes in the whole torus and use `dExt T`; they do not assert $T\ni z$, `IsDj`/polymer-domain membership, exact support, termwise locality in the datum, joint analyticity of a chosen coefficient family, reality, symmetry, or the paper's rate $\kappa_a$. The mark labels and `DetExpansionLocC.anchor` can support further root-incidence statements, but `toDetExpansionC` and `thm31aC_of_input_const` do not expose them. The existential $E_0$ is chosen after the datum, so analytic dependence on the datum does **not** follow from `E1MarksC` or this consumer. The result is Theorem 3.1(a)'s **whole-torus zero-class numerical expansion in this Lean interface**, conditional on the OPEN mark assembly; it is **not** the full source clause (a), nor the modular boundary case. **REFUTED:** calling the determinant record alone closes the source-level localization and analyticity clauses.

## T6. Ordered bounded leaves

1. **Start now, Sonnet, 100–160 lines:** specialize `D.covers` to `reads := fun _ => Set.univ`, physical `dom := polyDom …`, and prove `hdomR`; add the fixed `S/BS/hpS` definitional equalities. Also settle physical `bridgeFamily` nonemptiness, or prove a dummy-label construction with a positive budget reserve. **OPEN**.
2. **Start now, Sonnet, 100–160 lines:** `corrF0_pos`, `corrBudget_fromTower` with $\epsilon_B=1/(CPE+1)$, and a single `max` threshold combining the landed activity/radius/budget thresholds. Reuse `exists_beta0_corrR`, `exists_beta0_corrF0_le`, `bridgeFamily_entropy`. **OPEN**.
3. **Start now, strong, 130–210 lines:** finite rooted-output regularity for one chosen `DecMarkPair` family: measurable/continuous in $\Phi$, `DepOn` on a bridge, analytic in $(e,u)$, and the clamped versions on `ball 0 corrU`. Coordinate this with W510's `decMarkCorrTerm` statements; do not use W510 as landed until merged. **OPEN**.
4. **After W510/W512 and W505 land, strong, 180–260 lines:** specialize W510's corrected count to $F_0={\tt corrF0}$, prove the exact `hF` almost-everywhere identity from W512 with W505's total correction, `ae_hatOf_restr`, and the inactive cutoff. All use one pair family and $\rho=p_1$. **OPEN**.
5. **After 1–4, strong, 160–240 lines:** choose the common activity package once before $z$, build every `InterpMarks` field in the table, and seal `e1MarksC_zeroClass_fromTower`; add a small composition check at the exact `E1MarksC` type. **OPEN**.
6. **After 5, Sonnet, 80–140 lines:** specialize `detExpansionLocC_scale_fromTower`, apply `toDetExpansionC D.xi`, prove a fixed $B_L$ inequality, call both StepComplex consumers, and state the numerical zero-class output with its precise limitations. **OPEN**.

Confidence: high on the record field map, common-label/root-index separation, numerical threshold, and determinant conversion; medium on the physical bridge-family nonemptiness and the W512 same-pair identity, which remain OPEN. This is a blueprint, not a claim that the open theorem is proved.
