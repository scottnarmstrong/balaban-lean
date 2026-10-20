# Removal records in the post-R representation (W1148 audit of W1151's finding n₀)

## Verdict
**The double count is real in the landed definitions.** `D1Form2` sums `postTerm2` over `rep.hist`, and `IsComplete k (k+1)`
forces `rep.hist` to contain one history for every class of `Agree k (k+1)`, which compares the removal records `Rem_j`
(`LabHist.Agree`, `Def7Hist.lean:81`). A history that removes a ripe component at the scale `k` ends with `Z_k = ∅`
exactly like the trivial history, and the two have the same term.

## Evidence (Lean)
* `two_le_card_empty_region`, `two_le_card_empty_region_ripeRem` (`Spine/FinalRepRemoval.lean`, W1151): a complete set has at
  least two histories with empty region; the witness is the genuine-radii setting (trivial history and `ripeRemHistory`).
* `postTerm2_of_region_empty` (`Spine/FinalRepGroup.lean`): the term of a history with `Z_k = ∅` is `sfFactor2 C vc univ`
  (no operator, boundary sum empty). New: `postTerm2_eq_of_region_empty` (`Spine/RemovalHist.lean`): the terms of any two such
  histories are equal, whatever their removal records. So `ℬ'` cannot carry the removed gas for these histories; it is in
  `ℛ''`, which sits inside `sfFactor2` for every term.
* New: `exists_mem_agree_rem`, `exists_mem_rem_ne_empty`: a complete set contains a history with any given removal records;
  it cannot be thinned to histories without removals while keeping `IsComplete`.
* Nonempty `Z_k`: `postTerm2` reads the history only through `(A.H.step k).Z`, the components `PostComp A k` with their
  `localHistory` and labels, and `rep.B`. Two histories that differ by a removed component away from the supports of all kept
  components have the same `Z_k`, the same local histories and the same factors; a removed component is not a factor of the
  product over `PostComp`, so nothing vanishes. The double count is therefore not special to `Z_k = ∅` (argument from the
  definitions; I did not build the nonempty instance in Lean).

## Source
LFR D-III.8: the history set is all admissible histories with `R`-records in `{removed} ∪ 𝔎`, "terms with zero operator are
harmless", needed for the gas identity (Lemma III.10.4). P7 (3.26)–(3.29) sum the removed clusters into the exponent
(`ℬ'`, `ℛ''`): the post-`R` term of a kept configuration is one term with the gas in the exponent. "Harmless" holds if the
term of a history with a removed component is zero (the removed outcome has no kept operator). In Lean it is not zero: the
removed component simply disappears from `PostComp`. For `Z_k = ∅` there is no operator at all, so the zero-operator reading
fails literally. (I checked the printed P5 (1.21), (1.27) summary in `review/papers`; the exact index set of P7 (3.26) was
not re-read in the PDF.)

## Which spine inputs this affects
* `LastIntegralInput`/`FinalLargeFieldInput` (W1151): `∫ρ` contains `n₀ Ξ^sf`; stated form needs `n₀ = 1` (Lean: `lastRegionWeight_empty`).
* `RKeptGasInput` (`GasOutput`): requires `D1Form2` for `ρ'` and `∫ρ' = ∫ρ` together; with `n₀ ≥ 2` identical `Z_k = ∅` terms
  the gas `ℛ''` would have to absorb a constant factor `n₀`, which a local small remainder cannot do on tori of growing size.
  So the post-`R` form of the real `Rρ` does not satisfy `D1Form2` on the class where a ripe removal exists; the input is false
  or forces unnatural `ℛ''` there. Not proved in Lean.
* `RInput`, `ClassStepInput` (R part), `FrozenStepInput`, `TransferInput`: consume `D1Form2`/`GasOutput`; same effect.
* `BaseStepInput`: no ripe component exists at the first scales, so no removal record occurs; not affected.
* `IsRep2`/`IsRepPre2` for the pre-`R` class: `Rem` is empty there; not affected.

## Options (diffs are text, nothing applied)
(a) **Zero term for histories with removals.** In `Def7v2Form.lean`:
```
noncomputable def postTerm2 … : ℂ :=
  if ∀ j, j ≤ k → A.H.rem j = ∅ then
    gOp (fun c : PostComp A k => …) … 
  else 0
```
`IsComplete`, `Agree`, `rep.hist` unchanged. This is literally D-III.8's "terms with zero operator are harmless", now also for
`Z_k = ∅`. The gas of the removed clusters is in `ℬ'` and `ℛ''` of the kept histories (Lemma III.10.4).
Affected: `postTerm2` and its 7 direct users (`PostWeightSupport`, `LateParentR3`, `D1ParentDomain`, `InitialBetaBridge`,
`Def7v2Inhabited`, `FinalRepGroup`, `Def7v2Form`): each needs one case split with the removal-free branch equal to the old
statement; `PostConv2` is unchanged (a zero term converges); `n₀` becomes the number of removal-free empty-region histories.
(b) **Restrict the sum.** `D1Form2: ρ = Σ_{A ∈ rep.hist.filter (removal free)} …`, with completeness unchanged. Same effect,
but every statement about `Σ_{A ∈ rep.hist}` (12 files use `D1Form2`/`PostConv2`) changes shape. Larger.
(c) **Quotient by removal records** (complete set for `Agree` with `Rem` forgotten). Changes `IsComplete` (13 files), and the
term must be proved invariant on classes, which is false for histories whose local histories see the removed component.
Rejected.
(d) **Weight by `1/n`**: not a source object. Rejected.

## Recommendation
Option (a). It is one definition, matches the source wording, keeps `IsComplete` and all pre-`R` objects, and makes `n₀ = 1`
on the classes of the final step (trivial history is removal free; every other empty-region history has a removal).
Check before applying: the kept pre-`R` form (`preTerm2`) is untouched; the pin/budget/operator clauses range over `rep.hist`
and stay true (they are bounds on terms that are now zero for removal histories).

## Ruling text for Scott (plain language)
In the representation of the density after the large-field operation R, the sum runs over all histories, including histories
in which a large-field component was removed. The removed components are already accounted for in the new boundary terms and
the new small-field remainder, so a history with a removal must contribute nothing to the sum; as defined now it contributes
the same term as a history without the component, which counts the all-small-field term more than once (for the last step,
n₀ ≥ 2 times). Proposed ruling: the term of a post-R history is zero whenever the history has a removal record at some scale
j ≤ k (LFR D-III.8, "terms with zero operator are harmless"); the history set and its completeness are unchanged. Approve?
