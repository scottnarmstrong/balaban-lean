# Round 28: D7 migration and the open-to-fine tree

12 October 2026. Repository reads only. Status words concern the assertion immediately following them; proposed Lean code is **OPEN** until elaborated. Source checks: P1 `BF02099355.pdf` p. 117, (2.26)–(2.27); P5 `s002200050433 (1).pdf` pp. 496–497, (1.33)–(1.39); P6 `s002200050470.pdf` p. 34, (4.32)–(4.34). Their open-continuum conventions are recorded in `VMOD-26.md` §1.

## 1. Exact D7/H7 Lean migration brief

**PROVED code inventory.** `LargeField/Def7Hist.lean:304–320` defines `IsCovCurve` and raw coarse `dCovMod`; it admits continuous segments in unions of **closed** coarse cubes. `LargeField/Def7.lean:365–410` and `Def7v2Class.lean:95–140` are the only direct bound users. Both quantify over `bdryDoms (OmegaCube A.H k) (Zof A)`. `bdryDoms` (`Def7Hist.lean:291`) requires coarse `DmodOmega` and crossing $Z$, with no aligned-cover or finite-size condition. `DmodOmega` (`Geometry/DomainsMod.lean:60`) uses **coarse nearest-neighbour** complement components; `Fluctuation.DjMod` (`Fluctuation/SizeModDefs.lean:85`) uses **fine nearest-neighbour** components. The two need a resolution comparison, despite using the same adjacency name.

**OPEN implementation; exact proposed data.** Place this in a new `LargeField/Def7FineSize.lean` importing `Def7Hist`, `History/OmegaPost`, `Fluctuation/SizeModDefs`, and `Localization/CubeAligned`; avoid a cyclic import by checking the module graph before committing. The displayed binder syntax suppresses only ambient `S,n,R,k0,K,M` and typeclass binders:

```lean
structure FineSizeFrame (S : Setting) (n : ℕ → ℕ) (M K m₀ m₁ : ℕ) where
  N₁ : ℕ
  posN₁ : 0 < N₁
  hM : M = S.L ^ (m₀ + m₁)
  side : (N₁ * S.L ^ m₁) * S.L ^ K = M * n K * S.L ^ K
  divN₁ : S.L ^ m₀ ∣ N₁

def d7Pull (F : FineSizeFrame S n M K m₀ m₁) (j : ℕ)
    (Y : Set (Torus S.d (n j))) :
    Set (Localization.CTorus S.d S.L F.N₁ m₁ K) :=
  {x | Localization.castT F.side x ∈ fineSet M K j Y}

noncomputable def d7SizeE (F : FineSizeFrame S n M K m₀ m₁)
    (A : LabHist S n R k0 K) (k : ℕ) (X : Finset (Torus S.d (n k))) : ENNReal :=
  let Ωf := d7Pull F k (A.H.omegaPost k)
  let Xf := d7Pull F k (X : Set (Torus S.d (n k)))
  Fluctuation.dcovModE m₀ k Ωf Xf

noncomputable def d7Size (F : FineSizeFrame S n M K m₀ m₁)
    (A : LabHist S n R k0 K) (k : ℕ) (X : Finset (Torus S.d (n k))) : ℝ :=
  (d7SizeE F A k X).toReal

def FineValid (F : FineSizeFrame S n M K m₀ m₁)
    (A : LabHist S n R k0 K) (k : ℕ) (X : Finset (Torus S.d (n k))) : Prop :=
  Fluctuation.DjMod m₀ k (d7Pull F k (A.H.omegaPost k))
    (d7Pull F k (X : Set (Torus S.d (n k)))) ∧ d7SizeE F A k X ≠ ⊤

noncomputable def bdryDomsPost (F : FineSizeFrame S n M K m₀ m₁)
    (A : LabHist S n R k0 K) (k : ℕ) (Z : Set (Torus S.d (n k))) :=
  (bdryDoms (A.H.omegaPost k) Z).filter (FineValid F A k)
```

Here `F.posN₁` is passed explicitly to construct `[NeZero F.N₁]`; the class already carries `hkK : k ≤ K`, which the cell-partition lemmas need; `hM` is necessary for the $\pi_j$ cell side, not merely for torus cardinality. In the actual class family take $m₀=P6.m₀$, $m₁=C7.m₁$, $N₁=S.L^{m₀}n_K$, derive `side` from `hM6` and `Nat.mul_assoc`/`pow_add`, and derive `divN₁` by divisibility of a product. The cast is from `Localization.castT` (`CubeAligned.lean:37`), the fine lift from `fineSet` (`History/LocalHistory.lean:30`), and the post region from `RegionHistory.omegaPost` (`History/OmegaPost.lean:44`). **PROVED warning:** `.toReal(⊤)=0`; retain `FineValid` in the boundary binder. `Fluctuation.G2_X` (`SizeModEntropy.lean:155`) needs `DjMod` and an aligned active cell, so `FineValid` alone does not provide all its premises.

**PROVED obstruction to a blind replacement.** A coarse `bdryDoms` label need not be a union of fine aligned $\pi'_k$ boxes, so its fine `dcovModE` can equal $\top$. Replacing the exponent while retaining every coarse label would silently assign size zero to such a label. The correct post record therefore uses `bdryDomsPost`; add `support` saying `rep.B A X ... = 0` for raw post labels outside this filter. This support assertion for the physical representation is **OPEN-D7-BOUNDARY-LABEL-SUPPORT**. Reindexing the present raw-`OmegaCube` sum to the post sum is separately **OPEN-D7-POST-REINDEX**; do not infer it from `OmegaCube_subset_omegaPost` (`OmegaPost.lean:51`).

**OPEN design, preserving pre-R.** Keep existing `D7Bdry` and `D7Bdry2` as raw pre-R records. Add `D7BdryPost F ...` and `D7Bdry2Post F ...` with the same field formulas but `bdryDomsPost F A k (Zof A)` at every $X$ binder, the new support field, and `fac * exp (-rate * d7Size F A k X)` in `bound`. The historical `OmegaCube A.H j` occurrences **inside** `loc_hist` and `globalLH` remain unchanged pending the separate H7 history-transport audit; changing their meaning is not a consequence of the size migration. Add `D7Bdry2Post.toD7BdryPost` by the same `hSetB_subset_hSetB2` proof as landed `D7Bdry2.toD7Bdry` (`Def7v2Class.lean:155`). The physical `loc_field`, `real`, `analytic`, `rot`, `euclid` equations retain their formulas, though their quantified label types change. The full `loc_hist` hypothesis likewise retains its displayed old-history equalities and changes only the label binders. This is a proposed **post** class, not a proof of its physical producer.

**PROVED declaration audit and OPEN edit plan.** “Statement” includes a changed structure field or a changed proposition body, even where the printed theorem type changes only by reduction.

| File | Old $\to$ new statement or definition | Proof work |
|---|---|---|
| `Def7Hist.lean` | No existing statement; add `FineSizeFrame`, `d7Pull`, `d7SizeE`, `d7Size`, `FineValid`, `bdryDomsPost` in new file. | Prove the frame construction and cast/lift lemmas. |
| `Def7.lean` | Keep `D7Bdry`; add `D7BdryPost`; `IsRep.bdry : D7Bdry` $\to$ `D7BdryPost`; add `Rep.bdrySumPost`; post `integrand`/`postTerm`/`D1Form` use that sum, with pre `integrand` retained. | Rework post form definitions and constructors; `D7BdryPost.bound` has new exponent and finite binder. `PostConv` changes by its integrand body. |
| `Def7v2Class.lean` | Keep `D7Bdry2`, `D7Bdry2.toD7Bdry`; add post record and post transfer; `IsRep2.bdry : D7Bdry2` $\to$ `D7Bdry2Post`; `RepClass2` changes through its member proposition. | Post transfer reuses fieldwise projection, including the pinned-ball inclusion. |
| `Def7Inhabited.lean` | `wBdry` stays pre; add `wBdryPost`; post `wIsRep`, `wIsRepFlat`, post `nonempty_d7Bdry` analogue, `nonempty_isRep`, `nonempty_isRepFlat`, `nonempty_isRepFam`, `repClass_nonempty` acquire new post types. `wIsRepPre`, `nonempty_isRepPre`, `nonempty_isRepFamPre` stay raw. | Reuse zero proofs; provide a frame for `nK=1` in each existential and support-zero. |
| `Def7Variants.lean` | `IsRepPre.bdry : D7Bdry` stays; `IsRepFlat.bdry : D7Bdry` $\to$ `D7BdryPost`; `IsRepFam.member` changes through `IsRep`, `IsRepFamPre.member` remains pre. | `preTerm`/`D1PreForm` must still use raw `Rep.bdrySum`; flat constructor field changes. |
| `Def7v2Basic.lean` | `IsRep2.toFlat` result changes through `IsRepFlat2`; `IsRep2.mem_repClass2` through `RepClass2`; no direct size call. | `toFlat` keeps `bdry := h.bdry`; rebuild other projections. |
| `Def7v2Inhabited.lean` | `wBdry2` stays pre; add `wBdry2Post`; `wIsRep2` and its mass-split theorem change through post class; `wIsRepPre2` stays raw. | Zero bound and zero support; frame witnesses. |
| `Def7v2InhabitedFam.lean` | `wIsRepFlat2`, `wIsRepFam2`, post `nonempty_d7Bdry2` analogue, `nonempty_isRep2/Flat2/Fam2`, `repClass2_nonempty` change; pre family/nonempty remain raw. | Replace post `wBdry2` applications by post witness and rebuild. |
| `Def7v2Variants.lean` | `IsRepPre2.bdry : D7Bdry2` stays; `IsRepFlat2.bdry : D7Bdry2` $\to$ `D7Bdry2Post`; `IsRepFam2.member` changes, `IsRepFamPre2.member` stays. | Flat/family constructors rebuild. |

`Def7Basic.lean:303–320` also needs a rebuild: `IsRep.toFlat` still uses `bdry := h.bdry`. `Def7v2Form.lean:184` is an **additional direct edit**: split shared `integrand2` into pre and post versions and make `postTerm2` use `Rep.bdrySumPost`. The `Def7Variants.lean:53` pre term currently calls the shared `integrand`, so mutating that definition in place would incorrectly alter pre-R. `Def7v2Variants` has the analogous pre-form dependence. **PROVED grep audit:** repository-wide `rg` finds no other direct `dCovMod`/`IsCovCurve` users; `Rep.bdrySum` has exactly the `Def7.lean:247` and `Def7v2Form.lean:184` call sites. Consumers mentioning only `IsRep`, `IsRep2`, their variants, `D1Form`, or `RepClass` need rebuilds, subject to elaboration errors, not a size-specific proof edit. Keep the old `dCovMod`/`IsCovCurve` for historical pre-R meaning; after post migration their only operative uses are the two pre record bounds. Correct their comments so they do not claim to be the post paper size.

**PROVED non-vacuity at zero; OPEN nonzero test.** `Def7Inhabited.lean:84–90` defines `wRep.B=0`; `wBdry:180–193` proves `0<fac*exp(...)` by `positivity`. `Def7v2Inhabited.lean:219–231` does the same. New post witnesses reuse this proof, with support-zero automatic; there is no nonzero boundary witness in those files. Preserve the landed `nonempty_d7Bdry`, `nonempty_isRep/Pre/Flat/Fam/FamPre`, `repClass_nonempty` (`Def7Inhabited.lean:409–468`) and their v2 analogues (`Def7v2InhabitedFam.lean:120–164`), and add post-record nonempty theorems. A test with some `B≠0`, `FineValid`, finite `d7SizeE`, and genuinely nonempty boundary labels is **OPEN-D7-NONZERO-WITNESS**; zero witnesses establish logical consistency but do not test decay.

**OPEN engineering estimate.** Expect roughly 220–350 new lines for frame, post records, support, and transport; 100–180 edited lines across the class/form/witness files; 10–20 affected modules to rebuild. Green order: (1) add frame/accessors and their arithmetic proofs without changing a caller; (2) add post records, transfer, and zero witnesses; (3) split pre/post sums and integrands, prove zero-support equivalence for the witness; (4) switch `IsRep`/`IsRepFlat` and v2 records together with direct forms and witnesses; (5) rebuild dependent variants/basic/family files. The final physical support/reindex and H7 producer remain named open obligations even after a green build.

## 2. Open continuum tree to fine NN tree

**PROVED CONDITIONAL ON `OPEN-ALIGNED-LIFT-IDENTIFICATION` (geometric lemma).** Put $a=a_k=L^{m_0+m_1+k}$ in fine-site units. Assume the paper open domain $X^\circ$ is exactly a union of open, $a$-aligned $\pi'_k$ boxes of side $La$, and its landed lift $X_f$ is the union of all their half-open $a$-cells (the same identification for active cells and eligible boxes). Let $\Gamma\subset X^\circ$ be a finite connected rectifiable tree of length $\ell$ meeting every eligible open $\pi'_k$ box. Then a fine NN tree in $X_f$ meets every corresponding discrete box and has
$$\frac{|E|}{a}\le 8\,3^d\frac{\ell}{a}+2\,3^d.\tag{2.1}$$
The constants are $A=8\,3^d$, $B=2\,3^d$; with the P5 scaling identification $\ell/a=|\Gamma|_{\rm paper}/M$, they have the requested form. They are deliberately coarse and independent of the number of cover boxes.

**PROVED proof of (2.1) under the displayed lift hypothesis.** Let $V$ be the aligned $a$-cells whose closures meet $\Gamma$. At each $q\in\Gamma$, some open $\pi'_k$ box contains $q$; alignment means every $a$-cell incident at $q$ lies in that box's discrete lift. Thus $V\subset X_f$. As $\Gamma$ traverses cell faces, its consecutive cells are face adjacent. At a simultaneous crossing of two or more faces, *all* incident cells belong to $V$ and the same open box, giving a face-adjacent bridge. Hence $V$ is face connected. Traverse the tree twice, in length at most $2\ell$, and sample at arc-length intervals at most $a/4$. There are at most $8\ell/a+2$ samples. Every cell of $V$ meets a radius-$a/4$ ball about one sample, and each such ball meets at most $3^d$ aligned $a$-cells, also on the periodic torus. Therefore $|V|\le3^d(8\ell/a+2)$. Take a spanning tree of the face-adjacency graph of $V$; connect representative fine sites of adjacent cells by $a$ unit NN bonds inside their union, and prune cycles. The bond count is at most $a(|V|-1)$. If $\Gamma$ meets an eligible **open** box $B$, the touched $a$-cell at the meeting point is in $B$ by alignment; its representative meets the corresponding discrete box. This proves (2.1). Openness rules out the zero-length corner contact from `VMOD-25.md`: a corner lying outside a union of open boxes cannot serve as $\Gamma$. Interior overlap of adjacent open $\pi'_k$ boxes supplies the open corridor when the domain is connected; the counting bound itself uses openness and alignment, with no fixed-width corridor margin beyond one incident $a$-cell.

**PROVED CONDITIONAL ON `OPEN-ALIGNED-LIFT-IDENTIFICATION` and `OPEN-MOD-COMPONENT-COMPAT`.** If the active box correspondence holds, the tree just built meets every fine eligible box, so the fine **all-cover** modular size is at most $A d_k^{\rm P5,open}+B$. A tree meeting all eligible boxes is a `Fluctuation.ModAdmissible` witness after choosing those boxes; thus $\Delta=d7Size\le A d_k^{\rm P5,open}+B$, or $d_k^{\rm P5,open}\ge A^{-1}\Delta-B/A$. Here $a_*=1/(8\,3^d)$ and $b_*=1/4$ are explicit. Transferring P5's $B_0e^{-\kappa d_{\rm paper}}$ gives $B_0e^{\kappa/4}e^{-\kappa\Delta/(8\,3^d)}$, **not** the same $B_0,\kappa$; absorbing this into the D7 budget is **OPEN-D7-CONSTANT-REBASE**. Taking infima is valid even without an attained continuum minimizer. The full bridge `OPEN-PAPER-FINE-REALIZATION` remains **OPEN** because neither the exact open-to-discrete lift nor complement-component transport is landed.

**REFUTED without a component hypothesis.** Two closed complementary cells touching only at a corner form one continuum component of the closed hole but two NN components. `LargeField.DmodOmega` and `Fluctuation.DjMod` use NN components at different resolutions; neither alone identifies P5's continuum components. Require `OPEN-MOD-COMPONENT-COMPAT`: each continuum component of $(\Omega^\circ)^c$ has exactly one fine NN component in the lift, and containing/missing it is equivalent for each label. This condition, and the active/eligible-box part of `OPEN-ALIGNED-LIFT-IDENTIFICATION`, must be proved from the actual history geometry or imposed explicitly. The closed-cube `LargeField.dCovMod` cannot replace the open functional in this argument.

## 3. Remaining named statements

**OPEN.** Between a landed fine post-D7 clause and P5 (1.38)–(1.39)/P6 (4.32)–(4.34) remain `OPEN-ALIGNED-LIFT-IDENTIFICATION`, `OPEN-MOD-COMPONENT-COMPAT`, hence `OPEN-PAPER-FINE-REALIZATION`; `OPEN-D7-BOUNDARY-LABEL-SUPPORT` and `OPEN-D7-POST-REINDEX`; `OPEN-D7-CONSTANT-REBASE`; and `OPEN-D7-H7-POST-TRANSPORT` for the actual `globalLH` analytic domain and old/new fluctuation variables. The geometric estimate (2.1) is **PROVED CONDITIONAL ON** the named exact lift, while no physical nonzero boundary coefficient has been certified. The separate P6 analytic and coefficient producers listed in `VMOD-26.md` §4 remain **OPEN** and are not discharged by changing the size accessor.

**Confidence:** high in the landed-use inventory and conditional geometric estimate; medium in the proposed record split and line estimate; low in physical support, continuum-component transport, and the H7 producer, which remain open.
