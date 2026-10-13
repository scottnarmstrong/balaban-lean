# LOCC2: the remaining $C_2$ and fluctuation localization leaves

13 October 2026. This note reads the landed Lean tree and records exact targets. Statuses describe mathematical claims; proposed declarations are not yet landed. Write $G=G_p$, $a=\operatorname{compWeight}(L,a_1)$, $\epsilon=\texttt{eps}$, $\delta=\xi C_1(d)\epsilon$, $K_4=K4(d,L,N,BG,\kappa)$, $K_1=bgK1(d,L,N)$, $C_2=cK2(d,L,N)$, $C'_2=cK2'(d,L,N,\operatorname{famConst}(d,L,BG,\kappa))$, $m_*=3+(K_4+K_1)\xi C_1(d)$, and $b_*=3/2+(32/15)m_*$. The complete convention has $B=8\epsilon$; the $\nu$-free convention may use $B=3\epsilon/2$.

## 1. Exact targets and common setup

**PROVED.** Fluctuation/RenormExpG.lean:RenormExpInput.locC2 is exactly
~~~lean
∀ z, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa Kloc
  (fun _ ξ => pertClass G (cK * (cK2 d L N * (B * ‖ξ‖)))
    (bgK1 d L N * (xiC1 d * ε) + cK * cK2 d L N * B * r₀ + 2) (renMassU ν ξ))
  (fun _ v ξ => renC2On G a (blk z) ξ (renMassU ν ξ) v.2 v.1)
  (fun D ξ => ((F ((D.Ψ, D.h), ξ)).1,
    bgMultC G a ν (bgC0 d L N) D + (F ((D.Ψ, D.h), ξ)).2))
~~~
**PROVED.** The locDφ field in the same structure is exactly
~~~lean
∀ p, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (YsM p) dY κb Kloc
  (fun _ ξ => {v | SupBounds G v (cK * (cK2 d L N * (B * ‖ξ‖)))})
  (fun _ v _ => v p) (fun D ξ => (F ((D.Ψ, D.h), ξ)).1)
~~~
**PROVED.** RenormExpG.lean:HasLocPrinciple quantifies over every class-wide $M$
at fixed $\xi$, with one raw-data term analytic on expDom. The endpoint is the IsRenSol pair $F$, not the cut solution itself. RenormExpLemma35.lean:IsRenSol has analytic, solves, small, sup, unique fields; exists_isRenSol gives complete $B=8\epsilon$ subject to its explicit margins.
**PROVED.** Match RenormLocC1Zero.lean:renLocC1_zero_at: at block $z$, put
$X_1=X1(G,m_0,k,\operatorname{fam}(m_0,\operatorname{blockSite}(k,z)))$, blk z = blockSites … (k+1) k z, labels RenLabel G X₁, cubes renCube G X₁, Ys z = renYs (renCube G X₁) G m₀ X₁, and dY = renDY G m₀. For $p$, use the source half of renLoc_fin_domains and the analogous YsM p. The cut radius is $r_0$, the parameter radius $e^\kappa$, and Kloc = 1. RenormLocFibre.lean:RenLabel, renCube, renYs, renDY, renLoc_fin_domains, and renLoc_localization_expansion_fin are all landed.
**PROVED.** The last theorem requires CovSetup, cube membership/injection/disjointness,
the zero tree-length witness, $3\le d,L$, $0\le\kappa_0$, $3\kappa_0+3\le\kappa_d$, $4d(2L+1)^d\kappa_d\le\kappa$, $1\le(\kappa/2-1)/2$, the logarithmic size bound, and $\kappa_a,\kappa_b\le2\kappa_d$, as in renLocC1_zero_at.

## 2. Leaf 4: class bound

**PROVED CONDITIONAL ON OPEN renDec_sharp.** Set $r=\|\xi\|$,
$V=c_K C_2 B r$, $A=K_1\delta+c_K C_2B r_0+2$. Proposed renDec_pertClass takes FlCore, XiCOneReal D, $0<r_0\le1/16$, $\|\xi\|<r_0$, $\|s_P\|\le e^\kappa$, the leaf-3 bounds SupBounds G δφ_s (C′₂ b_* ε r) and Small G δα_s (C′₂ b_* ε r), and the named constant inequality
$$ c_K C_2 B\ge C'_2 b_*\epsilon. \tag{CB} $$
It yields SupBounds G δφ_s V and $(\delta\phi_s,\alpha_s+\delta\alpha_s)\in\operatorname{pertClass}(G,V,A,\nu_u)$, where α_s = decBgMult and the cut perturbation solves shifted renEdat.
**PROVED.** The field bound is (CB) times $r\ge0$.
RenormStrictData.lean:renDec_data_bounds_of_flCore gives $\ell_x^2|\alpha_s(x)|\le K_4\delta<1/2$ by FlCore.phi_lt. renSpacing_mass_le and renMassU_sub_norm_le give $\ell_x^2|\nu_u|\le1+(32/15)r_0\le17/15$. Thus $\ell_x^2|\alpha_s+\delta\alpha_s+\nu_u|<2+C'_2b_*\epsilon r\le A$. The nonnegative $K_1\delta$ adds room. RenormExpBounds.lean:pertClass uses α_s+δα_s as multiplier, with no extra mass shift.
**OPEN.** The C₁ template fixes $c_K=2+2K_4\xi C_1(d)$.
No landed theorem establishes (CB) for this value. Either prove a separate numerical restriction, or choose the shared constant $\max\{2+2K_4\xi C_1(d),\,C'_2b_*\epsilon/(C_2B)\}$. The denominator is positive in either convention. Whether the original value satisfies (CB) is **OPEN**: FlCore has no (CB) field or cited comparison lemma, and no numeric counterexample is established here.
**PROVED CONDITIONAL ON A SHORT NEW LEMMA.** Enlarging cK need not rebuild C₁.
Directly from RenormExpBounds.lean:bgClass, if $0\le c\le c'$, then bgClass G ν c D ⊆ bgClass G ν c′ D; use $c^2\le(c')^2$ for its last clause. HasLocPrinciple is antitone in its class argument: a bound on the larger class also bounds the smaller class. No landed named monotonicity lemma was found. Add that elementary lemma and transport renLocC1_zero to the enlarged cK.

## 3. Leaf 5: the endpoint

**PROVED.** RenormStrictData.lean:renEdat is
$(\bar\phi_s,\alpha_s+\Delta\nu,\epsilon\xi_0\Psi,\Delta\nu(h-\phi_s))$, with $\Delta\nu=\nu_u-\nu$. renEdat_decHyp_of_flCore gives mode false at $D_0=2K_4\delta+3r_0\le1$ and $D_1(r)=b_*\epsilon r$. renMargins_exists_r₀_of_flCore gives $r_0>0$, $r_0\le1/16$, $D_0\le\Delta_*$, $D_1(r_0)\le\Delta_*$ from $2K_4\delta<\Delta_*=\texttt{deltaStar'}(d,L,N,\operatorname{famConst},\gamma_1/8)$.
**PROVED.** Localization/DecoupledBackground.lean:i4b_one requires DecSpecs,
DGSetting, BgHyp, $\kappa\ge0$, family size, positive $\delta\le\epsilon\le bgC0$, $\delta\le c7$, mass inequality, InDomainC, and IsDecBg at all ones. It yields IsSmallSolution and exact bgFieldC = φ₁ and bgMultC = α₁. The unit-length equation in IsSmallSolution gives gdef G (barField G D.Ψ φ₁) = 0 on G.Ω 1.
**OPEN.** State renDec_one_unique with these i4b_one inputs,
$0<r_0\le r_F\le1/16$, both DecHyp margins $D_0,D_1(r_0)\le\Delta_*$, the leaf-2/3 mode-P DecFixed at $s=1$, Small G δα₁ (rho4 d L N BG κ), IsRenSol G a ν ε ε rF B F, XiCOneReal D, and $\|\xi\|<r_0$. Its conclusion is
$$ (\delta\phi_1,\delta\alpha_1)=F((D.\Psi,D.h),\xi), $$
where δφ₁ is dphi G (decG G a ν 1) on shifted renEdat.
More explicitly, put $E=\texttt{renEdat }\nu\,\epsilon\,D\,\phi_1\,\alpha_1\,\xi$ and
$F_s=\texttt{pertSource }G\,a\,E.2.2.1\,E.2.2.2$.
Name hDzero: $D_0\le1$, hDstar: $D_0\le\Delta_*$,
hDone: $D_1(r_0)\le\Delta_*$, hrF: $r_0\le r_F$,
hsmall: Small G δα₁ rho4, and hball: rho4 $\le$ c6.
The fixed-point binder is exactly
DecFixed G a ν (fun _ => 1) false E.2.1 E.1 Fs δα₁;
the claimed first component is dphi G (decG G a ν (fun _ => 1))
E.2.1 E.1 Fs δα₁. hbg names the IsDecBg witness at all ones.
**PROVED CONDITIONAL ON TWO NEW BRIDGES.** In
Background/ContractionCore.lean:Nmap the sole mode-P/U difference is
$(1/2)H_0\operatorname{gdef}(\bar\phi_1)$, hence zero here.
Prove a mode-U DecHyp and DecFixed from the mode-P data and this identity.
The landed isPerturbed_of_decFixed_one then applies at s=1; its small ball
is rho4 = c6′ … (gamma1 d / 8), by DecoupledBackground.lean:rho4.
Next use Background/Prop51Mass.lean:isPerturbedM_iff:
the reference-mass base is α₁+(νu−ν), while the complex-mass base is α₁.
Apply IsRenSol.unique in its c6 d L N ball after proving rho4 ≤ c6,
XiCOneReal → XiCOne, and $r_0\le r_F$.
No landed rho4 ≤ c6 declaration was found; rho4 alone does not typecheck unique.

## 4. Leaf 7: locality of the cut functionals

**PROVED.** Localization/RowsBg.lean:i4a_local_rows takes FamSpec,
DGSetting, HatConn, $\kappa\ge0$, family size, two cuts bounded by
$e^\kappa$, two mode-matched DecHyp at common $D_0,D_1$,
both margins $\le\Delta_*$, and
IsNnComp ((Vset X₁ 𝒞).filter Ω₁) Y.
Its cuts equal one off parCubes X₁, zero on parCubes X₁ \ 𝒞,
and agree on member cubes inside Y. It needs DataAgreeRows on SY G X₁ 𝒞 Y,
two DecFixed points and two Small bounds at c6′ … (gamma1 d / 8).
It concludes δα_s = δα_s′ on SY and δφ_s = δφ_s′ on Y,
each field written using dphi.
**PROVED CONDITIONAL ON OPEN leaves 2–3.** The DecHyp pair comes from
renEdat_decHyp_of_flCore, since RenC1Ag equates ξ and hence their D₁.
Small and DecFixed come from leaves 2–3.
FlCore.hS, .Sp, .hκ, .hM supply structural assumptions.
Fluctuation/RenormRowAgree.lean:renDec_row_agree gives DataAgreeRows
from RenC1Ag and the supported label cuts; rowSite_iff_of_potentials landed.
Its proof constructs the component and cut-support facts, but as local haves.
Extract a helper or repeat the short component and support argument.
**OPEN.** renC2_local_cut needs rootBlock_subset_SY:
each $x\in\texttt{blockSites}\cap\Omega_1$ belongs to SY.
No declaration of that name landed. Derive it from BlockMargin supplied
by levelLocalCover: its witness z_x has $x\in\operatorname{intBox}(z_x)$,
hatBox z_x ⊆ X₁ ⊆ Y, and no parameter cube in Qset z_x.
Thus z_x ∈ ZY and x ∈ SY for every cut family.
RowsBg.lean:rowSite_subset puts every row neighbour of renC2Site in Y;
rowSite_iff_of_potentials removes the dependence of RowSite on α.
Root α_s+δα_s agrees by C₁ background locality and i4a_local_rows;
the mass and ξ agree. Site equality yields renC2On equality.
**OPEN.** renDphi_local_cut reads only p ∈ Y.
The source part of renLoc_fin_domains puts p.1 ∈ X₁ ⊆ Y;
the dphi conclusion suffices. Both results must have
LocalityAEOn (Real.exp κ) with Ag := RenC1Ag (renCube G X₁) X₁,
as required by renLoc_localization_expansion_fin.

## 5. Leaf 8 and work order

**PROVED CONDITIONAL ON OPEN leaves 2–5,7.** Follow
RenormLocC1Zero.lean:renLocC1_zero_at for block and source roots.
Reuse its renLoc_fin_domains tuple, labels, Ag, AgY,
hrefl from renC1Ag_refl, hlink from renC1Ag_of_rawAgree,
the expand wrapper around renLoc_localization_expansion_fin,
and both calls expand expDom Eb₀ and expand Sξ M.
hana is leaf 2's single ambient analytic cut pair composed with
RenormExpG.lean:an_renC2On, or projection/evaluation for locDφ.
hbd on expDom is leaf 4 plus norm_renC2On_le_of_mem
or the SupBounds point bound; at fixed ξ it is the user's class-wide M.
hloc is leaf 7, hFeq is leaf 2, and the endpoint rewrite is leaf 5.
For C₂ one may use
$E_{b,2}=(17/32)N(3+A)V(r_0)^2\operatorname{blockWeight}(G,B_z)$;
for locDφ use $V(r_0)/\ell_p$ from SupBounds and positive spacing.
Kloc = 1 and output rates obey $\kappa_a,\kappa_b\le2\kappa_d$.
**OPEN.** Ordered Lean leaves: (4a) class arithmetic and monotonicity,
about 100 lines, Sonnet, starts now; (5a) mode bridge and rho4 ≤ c6,
about 160 lines, strong, starts now; (5b) endpoint identification,
about 150 lines, strong, starts with leaf-2 statement as a hypothesis;
(7a) root SY geometry and row comparison, about 180 lines, strong,
starts now with leaf-3 bounds as hypotheses; (7b) two LocalityAEOn wrappers,
about 180 lines, Sonnet after 7a; (8a) C₂ expansion, about 260 lines,
strong after 2–5 and 7; (8b) source expansion, about 220 lines,
Sonnet after 2–5 and 7. Each task stays below 300 lines.
The remaining substantive risks are (CB), the uniform class bound
for the full analytic family, and the two endpoint bridges.
Confidence: high for signature matching and row geometry;
medium for endpoint bridges; low for (CB) at the original shared cK.
