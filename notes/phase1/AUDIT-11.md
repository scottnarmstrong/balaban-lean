# AUDIT-11 — site records and packaging

**Verdict:** The regrouping and the two site-record theorems are **FAITHFUL as conditional statements**. Applying the physical `E₀` record to the coefficient family currently returned by the tower is **WEAKER THAN CLAIMED** if asserted today: that family has thick locality, while the new record assumes exact site locality. The sharp mark lemmas establish a needed leaf but are not, by themselves, a new tower coefficient theorem. No declaration inspected is inherently **VACUOUS**.

## Scope and frozen input

Tier-2, refute-first statement/definition audit only; `/home/scott/Balaban` was read-only, with no build. Main was clean at commit `6fa45d77032cb193d5b9c8c760c175fa980f05ec` (2026-10-13); `RenormE1SiteRecord.lean` was already on main, so no branch fallback was needed. These SHA-256 hashes freeze the line anchors below:

| File (`Balaban/` prefix) | SHA-256 |
|---|---|
| `Fluctuation/CoeffFamilyLocExp.lean` | `03f111895de7979e88904cf39abbe3a4ac808f030fd7eebdfbf1d41429879d35` |
| `Inhabited/RenormE1SiteRecord.lean` | `49087822df95eddd2e0aa7c22671424777ec9f4969542f90ad5222caa13f57aa` |
| `Inhabited/E1ParamRawLocal.lean` | `78657166e7d32d31dd48a20a79121749b8bf2b91412c96d735d9bb8923d822df` |
| `Inhabited/E1CoeffFamily.lean` | `f4d25a3875379d6111ce33f54fcc4dab4a78c1cc14754045b4f1f456dda38276` |
| `Inhabited/RenormHalfDetOnly.lean` | `60c6860f79d5a345857dc8c6dc529c67ef8118b8e90c04a6e730e1a3dee5cf74` |
| `Fluctuation/RenormExpCauchy.lean` | `21408d054cedb8a1aeaa7ffcfba767b3d0b0c2fd75e236c9a088c240fa63baab` |
| `Fluctuation/RawAgreeSites.lean` | `5e49bc86579739c1fa002e06af3bff351e3195a342d0a4d9b39dd11cadd0be2d` |
| `Fluctuation/HatLabelsDep.lean` | `376b990fab67f1b35e05d3f67a635570672247695bd06350acf6ec4f2c5b16e4` |
| `Fluctuation/StepComplexOut.lean` | `df16d2de12afbbf7594f28e103b48a1df7171dc46e306a0486cc98223925463c` |
| `Inhabited/StepTower.lean` | `015b9f8321e12a9bd8ce016439ca178ba42b8edc8b55315ee2176e985e25f6ef` |
| `Fluctuation/MarkFibreSitesOf.lean` | `bf371a4261ad154fe38cd325853042fd3df387c92081a27856536adc464c7402` |
| `Fluctuation/RenormThetaDatum.lean` | `b7662ce278c59a6daded9f3f872fdf8a695f3014a48594bf970d8b0d94692132` |
| `SmallField/Def6Terms.lean` | `a0c93ce2410aebac4b2803cdb5cdde0ebcab8ea0247494ca102d2600c4056e4f` |
| `Fluctuation/RenormExpInputOn.lean` | `711a680d451d5585f7086fb8509dfb29c841cbc6c9c129a6fb5cc01d25471aa4` |
| `Fluctuation/MarkedRootGeometry.lean` | `ec4af6441ed734078746a6aa4df0bcddd98c68f81fd7328b0352dc708dfe023a` |
| `Fluctuation/ParamActivityPhysical.lean` | `84441f87d4568ac2ba7bab2aaa590fbfdbaae39c8ae5e92f9b500b90c7113f9a` |

## L1 — coefficient family to site expansion: FAITHFUL

The four hypotheses are compatible with nonzero coefficients. `physRestrict A` returns `(Ψ(x),h(x),g(x))` at each `x∈A`; its equality is *exactly* raw agreement of both components plus source equality [ParamActivityPhysical.lean:356–361; RawAgreeSites.lean:65–92]. For any polymer cube set `T₀`, the constant family `c θ T = (if T=T₀ then 1 else 0)` is nonzero, analytic, exactly local, supported on polymers, and obeys the bound with `B=exp(κ*dExt T₀)`. This defeats the proposed degeneracy. It does not show the physical tower family has exact locality.

`exists_rawProj` returns a continuous linear retraction `P` onto `rawSub`, potentially mixing sites away from that subspace [CoeffFamilyLocExp.lean:118–125]. The term `c (P q.1,g₀) T` is only asserted local for `q,q'∈expDom`, and `expDom` forces `q.1=rawOf D`; thus `P` is the identity at every point where `IsLocExp.local_` is required [RenormExpCauchy.lean:70–92; CoeffFamilyLocExp.lean:151–177]. The renormalized version uses `P` on `rawOf (renThetaDatum D ξ)`, again in `rawSub`, and the same `ξ` plus `RawAgree Y` preserves the sitewise rescaling [CoeffFamilyLocExp.lean:207–245; RenormThetaDatum.lean:71–85]. No global sitewise property of `P` is claimed.

`sum_eq` partitions the finite cube-set sum by the image of `T↦sitesOf T`, with no duplicate outer site labels; in fact this map is injective under `L^m₀∣N₁` [CoeffFamilyLocExp.lean:65–100; MarkFibreSitesOf.lean:42–58]. The image also contains empty or disconnected site sets, but their coefficients vanish by support; `IsPolyDom` requires nonempty connected sets [Def6Terms.lean:93–97]. The tower corollary takes `Dom=XiCOneReal(...,R.t/2)`, `r=R.r₀`, and chart radius `R.t` for the renormalized datum [CoeffFamilyLocExp.lean:260–304], matching the determinant fibre record [RenormHalfDetOnly.lean:94–124]. That determinant result also supplies a base datum in the fibre [RenormHalfDetOnly.lean:111–115], so the intended fibre is not merely a formally empty domain.

## L2 — marked and combined site records: conditional FAITHFUL

`renE1_siteRecord_of_family` uses a `dite` to define the value function outside the constant-`h₀` fibre, but its `Dom` includes that condition. `sum_eq` quantifies only over `D∈Dom`; its proof selects the true branch and invokes `hval` at `renThetaDatum D ξ`, whose `h` is unchanged [RenormE1SiteRecord.lean:58–92; RenormThetaDatum.lean:81–85; RenormExpCauchy.lean:84–92]. The `else 0` branch is never used to identify physical energy.

The marked value is `(S.withDatum (renThetaDatum S (t/2) D ξ) hD).E1locC zeroClass z`, and the combined value is the same step's `E0locC` [RenormE1SiteRecord.lean:74–77, 165–168]. By definition `E0locC = -½ Σ logAC + E1locC` [StepComplexOut.lean:182–185]. The determinant-only record instead supplies `RenormExpInputOn.expE0` with `renE0θ_det (t/2) E`, a sum of determinant terms only [RenormHalfDetOnly.lean:72–107; RenormExpInputOn.lean:90–91]. Thus they occupy the same *function slot*, but are not the same function; the new combined record has the physical `E0locC` value only on its stated fibre. Reading the determinant-only input as already physical would be **WRONG OBJECT**.

`renE0θ_det_eq_logAC` holds for `D∈XiCOneReal(...,t/2)` with constant `h=h₀` and `‖ξ‖<R.r₀`; the chart lift reaches the determinant record's radius `2t` [RenormE1SiteRecord.lean:97–112]. `add_union` combines the determinant collar family and the site family at rate `min (3/2 R.κdec) κ` with constant `hullConst(3,3,towerDetRate R.κ,towerDetConst R.κ)*exp(c1 3 3*log 2)*exp(hullRate(3,3,towerDetRate R.κ)) + B` [RenormE1SiteRecord.lean:151–185]. For the tower family, take `κ=R.κ'` and `B=K0 3 3 R.κ0`; since `κ'=(3/2)κdec+κ0+1` and `κ0≥0`, the minimum is `(3/2)κdec` [StepTower.lean:34–45].

The tower coefficient theorem provides the same analytic form on `physV`, a stronger bound for **all** cube sets (hence the polymer-set premise), support with an additional root-cube condition, and the same constant-field `E1locC` sum at chart radius `t` [E1CoeffFamily.lean:285–321]. Its assumptions include `m₀=1`, `3∣N₁`, `5<N₁`, `0<ν`, and the stated threshold/scale data [E1CoeffFamily.lean:236–242]; the site record takes `m₀=1`, `3∣N₁` and the determinant union also requires `5<N₁` [RenormE1SiteRecord.lean:35–64, 120–150]. **Surviving gap:** the tower's locality clause is on `thickSet (Yhat univ (sitesOf C))`, not `sitesOf C`; the new theorem explicitly assumes the latter [E1CoeffFamily.lean:301–308; RenormE1SiteRecord.lean:45–51, 131–137]. No implication from that thick clause to exact locality is available.

## L3 — raw-Y mark bridge: FAITHFUL locally, not yet the tower instance

`S.hatOf m₀ ρ hp Φ` clamps a coordinate of `Φ` at `S.cellOf m₀`; its definition has no datum argument [HatLabelsDep.lean:65–69]. Both calls of `evDec_local_rawY` use that same function, so hat agreement is discharged by `rfl` [E1ParamRawLocal.lean:475–489, 493–507, 563–581]. The corrected mark and rooted-output proofs use `agreeOn_mono` in the right direction: a contributing label `Y` lies in its bridge `Y'` by `subset_bridge`, and the anchor/bridge lies in `sitesOf T`; hence agreement on `sitesOf T` restricts to `Y'` and then `Y` [E1ParamRawLocal.lean:243–261, 575–581, 620–629; MarkedRootGeometry.lean:113–122]. The sharp `hG` lemma has explicit `hF₁,hSol` premises [E1ParamRawLocal.lean:535–551, 589–626]; the selected tower pair in the current coefficient theorem is still consumed through the old thick pair interface [E1CoeffFamily.lean:412–445]. This is a bridge to integrate, not an already packaged exact tower family.

## Refutation ledger and wording

| Challenge | Refutation result |
|---|---|
| Exact locality forces zero | **Refuted** by a nonzero constant coefficient on one polymer set; locality compares all three physical fields on its sites. |
| A site-mixing `P` spoils `local_` | **Refuted** on the quantified `expDom`; no assertion outside it. |
| Regrouping counts a cube set twice | **Refuted** by finite image/fibre partition and injectivity. |
| `else 0` changes the claimed physical value | **Refuted** because `sum_eq` is fibre-restricted. |
| Determinant-only `expE0` already is the physical `E₀` | **Survives as a wrong-object reading**; its value is `renE0θ_det`, while the combined record uses `E0locC`. |
| Current tower `c` meets exact `hloc` | **Survives as a weaker-than-claimed application**; its exposed `hloc` is thick. |

The two theorem docstrings needing the clearest caveat are `RenormE1SiteRecord.lean:33–34` and `:114–119`. Suggested replacements: “**Conditional marked site record:** given a coefficient family with exact locality on `sitesOf T` and the stated analytic, bound, support and value hypotheses, the renormalized marked energy has this expansion on the constant-field fibre.” “**Conditional physical E₀ site record:** adding that marked record to the determinant collar record yields the physical `E0locC` expansion on the fibre; the current tower coefficient theorem still supplies only thick locality.”

Closeout: all named statements and consumer definitions were inspected at the frozen revision; the two application/object cautions survived the explicit refutations above. Proof elaboration, axiom status, and mathematical estimates were outside scope; no build was run.
