# FLUCTUATION: one small-field step in full at $\lambda=\infty$ (phase 1, document D-FLUCT; roadmap I-8, I-9; open item O-2′)

**Version 2.1** (2026-10-12). [v2.1] Follow-up: Lemma 2.5's indicator arithmetic is repaired, and Theorem 3.1(f)'s old-action status is refined against VMOD §2 and P6 (2.14), (2.19). Brief: `orchestration/briefs/D-FLUCT-fluctuation.md`. Status: working repair of the independent FL-A01–FL-A13 audit; nothing here is approved or frozen. Mathematics on paper only; no Lean was written or run in this directory. Status labels throughout mean **proved** (the displayed argument closes without an open input), **proved conditional on a PROVED cited result** (the cited theorem has the stated hypotheses and conclusion), and **conditional on an OPEN assertion** (the assertion is named at the point of use). A Lean theorem about an abstract interface does not prove that this RG step satisfies its premises. Document key: **FL** (this document); SF = `SMALLFIELD.md` v3, LOC = `LOCALIZATION.md` v3,
BG = `BACKGROUND.md` v2, PE = `POLYMER.md`, GR = `GREEN.md`, LFR = `LF-RECONSTRUCTION.md` (Parts I–IV), OBS = `OBSERVABLES.md`.

**What was read.** AGENTS.md; the brief; SF (all, v3); LOC (all, v3); PE §§0–6; BG §§1, 5, 6; GR §3 (G-1 … G-6); LFR §II.0, §§II.2–II.3,
§II.5.5, §II.6, §II.7, §IV.0, §IV.1, §IV.2, §IV.5.4–IV.5.6, §IV.O; OBS §0 and headings; the reviews `review/papers/P4-*`, `P6-*`; ERRATA rows
ER-058…ER-070, ER-085…ER-104. **Sources.** P4 = CMP 182 (1996) 675 is a scan: **page images read** pp. 683–691, 694–706, 712, 718 (pdf pages
9–17, 20–32, 38, 44: the step (2.1)–(2.41), the new contributions (2.51)–(2.63) with Propositions 2.1, 2.2, the scaling (3.1)–(3.2), the
renormalization (4.1)–(4.24) with Propositions 4.1, 4.2, the bound (5.15)–(5.17), and (5.37)–(5.41) with Proposition 5.2). P5 = CMP 196
(1998) 485: text layer, pp. 494–521 in full (§1 end, §2, §3). P6 = CMP 198 (1998) 1: text layer, pp. 1–15 (§1, §2) and 21–45 (end of §3,
§4) in full. Landed Lean read (statements only): `Balaban/Localization/AbstractExpansion.lean` (`abstract_expansion`),
`TreeLengthCov.lean` (`treeLenCov`, `treeLenCovOne`, `gm2`), `PolymerCount.lean` (`gm3`, `gm4`), the `Decoupled*` files (`dg1`…`dg6`,
`i4a_*`, `i4b_*`), `Balaban/Polymer/{PE,Local,Holomorphic,Mayer,MayerPE,MayerMarked,Marked,Hole,Lattice}.lean` (`pe_xi_eq_exp`,
`pe_PY_bound`, `mayer_pe`, `mayer_marked`, `norm_D1_Ff_le`, `pe_hole`), `Balaban/Flow/{RGEquations,RGInfty,MatrixInfty,MatrixFree}.lean`
(`exists_rg_solution_triangular`, `rg_step_infty`, `rg_flow_infty`, `tendsto_rg_solution`, `matrixInfty`, `matrixFree`, `matrixSel`),
`Balaban/Multiscale/Constrained.lean` (`constrainedOp`), `Balaban/SmallField/Xi.lean` (`Xi`, `XiC`, `GapE`),
`Balaban/SmallField/RenormTheorem.lean` (`renormalization_local`, the landed I-6 local form).

**[v2 source check]** The v2 repair is anchored to the independent audit `notes/phase1/FLUCT-AUDIT-astra.md` (SHA-256 `baeda7ea93ace96b95b180ef293787e10b00e00a397c34097ec53137ac3f5b1d`) of the unchanged version-1 source (SHA-256 `860d4b39e44d96a21d26d9dad4ef008bfd6ac9281b18537f5b2565b19763fb2a`). I read the statements of `RenormTermwise*.lean`, `Polymer/MayerMarked.lean`, `Localization/I5.lean`, `SmallField/XiProps.lean`, `XiComposeField.lean`, and the draft `SmallField/Def6.lean` in the read-only Balaban tree. Their abstract conclusions and premises are distinguished in §1.3. The formulas newly used in §4 are checked against LFR Definition II.3.5 and the P5/P6 text layers; P4 (4.19) on printed p. 704 and (5.39)–(5.41) on printed p. 718 were checked against PDF images. No conclusion is drawn from the unreliable P1–P4 OCR.

---

## 0. Summary

*(Written last; see the end of the drafting log in §6.6. This section is the reply asked for by the brief.)*

**Statements and status [v2: FL-A01–FL-A13].** “Conditional on a PROVED cited result” names an abstract theorem whose premises are verified here; “conditional on an OPEN assertion” names a remaining mathematical input. A target estimate is not counted as proved merely because its abstract Lean interface is landed.

| # | Statement | Status |
|---|---|---|
| Def 1.1, Lemma 1.2 | modular covering size and finite $d_\Omega$ on every nonempty support; (G1)–(G5) | finite extension and (G1)–(G3) arithmetic proved here; source geometry for connected covers conditional on cited P5/P6 geometry |
| Def 2.1, Lemmas 2.2–2.5, Prop 2.6 | Gaussian step, chord identity, covariance, product measure and interpolation | algebra proved; Lemma 2.5's separate indicator margins checked [v2.1]; analytic/covariance conclusions conditional on PROVED cited BG/GR results and their stated input domains |
| §2.7 | subdomain decomposition P5 §§2–3 | cited P5; transfer to amended class conditional on OPEN cover/NC |
| Def 2.7, Lemma 2.8 | auxiliary generating set and margins | definition; margins conditional on OPEN assertion, VMOD.md |
| Lemma 2.9 | switch at $k_0$ | scalar chord identity and $O(\beta^{-1})$ cost proved; joint $\xi$/RG part conditional on OPEN RGFREE.md |
| Thm 3.1 (a)–(e), (g), (h) | I-8 expansions | conditional on OPEN cover/NC, fluctuation I-5 and, for (c), (Vmod) |
| Thm 3.1 (f) | old action/background changes | [v2.1] restriction algebra, abstract star cost and conditional H7 absorption proved; actual old-term/H7 mass domain, mixed cover, Vmod and resummation OPEN (VMOD §2, §3.6 here) |
| Lemma 3.2 | termwise I-6 on $X\cup\operatorname{st}_+(y)$ and (3.2) | proved conditional on PROVED landed `RenormTermwise*` declarations and their explicit `PremisesTerm`/`SumConds`; actual RG premises remain to be instantiated |
| (V0), (Vmod), Prop 3.3 | scaled and modular I-5; localized interaction | (V0) domain reduction checked; full fluctuation and modular inputs OPEN, VMOD.md |
| Thm 3.4 | one and two marks, finite support size | proved conditional on PROVED `mayer_marked`, Lemma 1.2, and the stronger two-mark slack $\varepsilon_H\le\varepsilon_{\rm PE}/4$ |
| Lemma 3.5; (IC) | exact renormalization identity; rate arithmetic | proved algebraically |
| Lemma 4.1 | weighted far-data response | conditional on the stated LOC weighted response/NC input |
| Thm 4.2, Cor 4.3 | O-2′ and related background changes | complex prefactor and (Λ28′) proved under stated H7/LOC inputs; full decoupled cover/NC OPEN |
| Thms 5.1, 5.2 | amended-class I-9 and recursion | conditional on OPEN I-8, VMOD.md and RGFREE.md; quantifier order corrected |
| Thm 5.3, Lemma 5.8 | family (CONT) and its preservation | family implication proved under common working neighbourhoods and OPEN step/RG inputs; `ContAtZero` alone does not supply those neighbourhoods |
| Thm 5.4 | subdomain step | conditional on OPEN (Vmod), Thm 3.1(f), cover/NC and stated P1/P5 transfers |
| Lemmas 5.5–5.7 | cutoff/domain/(B1) estimates | conditional on their stated cited P4, BG and LOC inputs; (DL-gap) is explicit |

**Remaining dependencies [v2: FL-A13].** The amended $\Xi^c$ class is the stated input (§1.4; landed draft Def-6 and accepted LFR Def-7 amendment). The complete I-8/I-9 chain still needs the auxiliary cover, NC and modular/fluctuation I-5 (notes/phase1/VMOD.md (in preparation)); the old-action expansion (same document); and the actual $\nu$-free divided RG system and switch derivatives (notes/phase1/RGFREE.md (in preparation)). The base $k=0$ covariance analogue and the cited P1 counterterm bounds remain separate inputs. The family limit needs the common Cauchy neighbourhood condition of Theorem 5.3 in addition to the bare `ContAtZero` clause.

**Lean scope.** §6.4 records a proposed module order, not a proof status. The termwise I-6 declarations are now landed, while the RG-to-`PremisesTerm` identification, the new cover and the full I-5 variants are not. No claim of a complete Lean fluctuation step is made here.

---

## 1. Conventions, inputs, constants

### 1.1 Units and lattices

At the step $k\to k+1$ we write formulas in the units of P4–P6 ("$\eta$-units"): $\eta=L^{-k}$; $T_\eta$ is the fine lattice (spacing $\eta$);
$T^{(j)}_{L^j\eta}$ the lattice of $j$-block centres, rescaled to the unit lattice $T^{(j)}_1$; at the step the old spin $\psi=\psi_k$ lives on
$T^{(k)}_1$ (spacing $1$), the new block variable $\theta$ on $T^{(k+1)}_L$ (spacing $L$, blocks $B_{k+1}(z)$ of $L^d$ unit sites), and after the
scaling $S^{(k)}$ the new spin $\psi_{k+1}$ lives on $T^{(k+1)}_1$. Norms: $\|f\|^2=\sum_{x\in T^{(k)}_1}|f(x)|^2$ on the unit lattice,
$\|f\|_L^2=L^d\sum_{z\in T^{(k+1)}_L}|f(z)|^2$ on the block lattice, $\|\cdot\|_\eta$ with weight $\eta^d$ on $T_\eta$. The dictionary with the fine
units of BG and LOC (fine spacing $1$, $\ell_j=L^j$) is LFR §II.0 ("Conventions of Part II"): $|\partial^\eta\phi|<\delta$ is $\ell_k|\partial\phi|<\delta$, and
the $\eta$-unit action at scale $k$ is $L^{-k(d-2)}$ times BG's action (1.2) with the weights $a_n$ and mass $\mu=\nu_kL^{-2k}$. Complex fields
use the **bilinear** product $u\cdot v=\sum_iu^iv^i$. Cubes: $\pi_j$ = partition into cubes of side $M$ (in scale-$j$ units, i.e. $ML^j$ fine sites),
$\pi'_j$ = the cover by cubes of side $LM$ that are unions of $L^d$ cubes of $\pi_j$ (P5 p. 502); $\mathcal D_j$ = connected unions of
$\pi'_j$-cubes; $n_\pi(X)$ = number of $\pi_j$-cubes in $X$.

### 1.2 The covering size functional, also modulo a hole

LOC v3 (§4.0, "Version 3 changes") replaces P1's tree length by the covering functional; we use it everywhere. For $X\in\mathcal D_j$ a *chosen
family* is a set $\mathcal K$ of $\pi'_j$-cubes contained in $X$ with union $X$, and
$$d^{\rm cov}_j(X)=\inf_{\mathcal K}\ \inf\{M^{-1}|\Gamma|:\ \Gamma\subset X\ \text{a tree meeting every cube of }\mathcal K\}$$
(lengths in scale-$j$ units; landed `treeLenCovOne`; the multiscale $\tilde d^{\rm cov}$ is `treeLenCov`). For the holes of P5 we need the
modular version. Let $\Omega$ be a union of $\pi_j$-cubes. P5 (1.33) [checked p. 496]: $\mathcal D_j(\bmod\,\Omega^c)$ is the set of $X\in\mathcal D_j$ that
contain or miss each connected component of $\Omega^c$.

**Definition 1.1 (modular covering size).** For $X\in\mathcal D_j(\bmod\,\Omega^c)$ with $X\cap\Omega\ne\varnothing$,
$$d^{\rm cov}_j(X\bmod\Omega^c):=\inf\big\{M^{-1}|\Gamma|:\ \mathcal K\ \text{a set of }\pi'_j\text{-cubes contained in }X\text{ whose union contains }X\cap\Omega,\ \ \Gamma\subset X\ \text{a tree meeting every cube of }\mathcal K\big\}.$$
For a nonempty set $S$ of $\pi_j$-cubes of $\Omega$ let $\hat Y(S)$ be $S$ together with all components of $\Omega^c$ adjacent to $S$. **[v2: FL-A12]** Fix $\kappa_0>0$ as in §1.5, put $B_\Omega:=|\{\pi_j\text{-cubes in }\Omega\}|$ and
$$D_\Omega:=B_\Omega+\kappa_0^{-1}B_\Omega\log2+\max_{\varnothing\ne T\subset\Omega,\ \hat Y(T)\text{ connected}}d^{\rm cov}_j(\hat Y(T)\bmod\Omega^c),\qquad d_\Omega(S):=\begin{cases}d^{\rm cov}_j(\hat Y(S)\bmod\Omega^c),&\hat Y(S)\text{ connected},\\D_\Omega,&\hat Y(S)\text{ disconnected}.\end{cases}$$
The maximum is finite on each finite torus, and the family in it contains every singleton. This is a finite real extension, exactly equal to the original modular size on every support that occurs in a connected cluster. Its large value on disconnected supports is used only to instantiate the all-support hypotheses of the landed Mayer theorem; it does not introduce an activity on such a support.

P5's $d_j(X\bmod\Omega^c)$ (1.34) asks the tree to meet every cover cube meeting $X\cap\Omega$; those contained in $X$ form an admissible $\mathcal K$,
so $d^{\rm cov}_j(X\bmod\Omega^c)\le d_j(X\bmod\Omega^c)$, and for $X\subset\Omega$ the definition reduces to $d^{\rm cov}_j(X)$.

**Lemma 1.2 (geometry of the covering sizes; proved).** Let $c_1:=(2L+3)^d$ and $c_G:=2dL$. For $X,X_1,X_2\in\mathcal D_j(\bmod\,\Omega^c)$ and sets
$S,S_1,S_2$ of $\pi_j$-cubes of $\Omega$:

- **(G1)** $n_\pi(X\cap\Omega)\le c_1\,(1+d^{\rm cov}_j(X\bmod\Omega^c))$; for **every nonempty** support $S\subset\Omega$, $|S|\le c_1(1+d_\Omega(S))$; in particular $|X|\le((2L+3)M)^d(1+d^{\rm cov}_j(X))$ (P6 (4.11) for $d^{\rm cov}$).
- **(G2)** There are $a_{\rm ent}=a_{\rm ent}(d,L)$ and, for $\kappa_0\ge a_{\rm ent}+1$, a constant $K_0=K_0(d,L,\kappa_0)$ such that for every $\pi_j$-cube
  $\square\subset\Omega$: $\sum_{X\ni\square}e^{-\kappa_0d^{\rm cov}_j(X\bmod\Omega^c)}\le K_0$ and $\sum_{S\ni\square}e^{-\kappa_0d_\Omega(S)}\le K_0$ (P5 (1.35)).
- **(G3)** If $X_1\cap X_2$ contains a $\pi_j$-cube of $\Omega$ then $X_1\cup X_2\in\mathcal D_j(\bmod\,\Omega^c)$ and
  $d^{\rm cov}_j(X_1\cup X_2\bmod\Omega^c)\le d^{\rm cov}_j(X_1\bmod\Omega^c)+d^{\rm cov}_j(X_2\bmod\Omega^c)+c_G$; the same for $d_\Omega(S_1\cup S_2)$ when
  $S_1\cap S_2\ne\varnothing$ (P6 p. 37).
- **(G4)** If $Y\in\mathcal D_j$ is connected with $Y\cap\Omega=S\ne\varnothing$, then $Y\subset\hat Y(S)$ and $d_\Omega(S)\le d^{\rm cov}_j(Y)$; if moreover
  $Y\in\mathcal D_j(\bmod\,\Omega^c)$ then $d_\Omega(S)\le d^{\rm cov}_j(Y\bmod\Omega^c)$.
- **(G5)** Any two points $x,x'$ of $X\in\mathcal D_j$ satisfy $|x-x'|\le M(d^{\rm cov}_j(X)+2\sqrt d\,L)$ (replaces P1 (3.54) in P4 (5.16)–(5.17)).

*Proof.* **[v2: FL-A12]** If $\hat Y(S)$ is connected, apply the first (G1) inequality to $X=\hat Y(S)$, whose intersection with $\Omega$ is $S$. For a disconnected $\hat Y(S)$, $|S|\le B_\Omega\le D_\Omega\le c_1(1+d_\Omega(S))$, proving its (G1). At most $2^{B_\Omega}$ supports contain a fixed cube, and their total disconnected contribution to (G2) is at most $2^{B_\Omega}e^{-\kappa_0D_\Omega}\le1$. Enlarge the constant obtained for connected supports by one. If $S_1\cap S_2\ne\varnothing$ and both $\hat Y(S_i)$ are connected, their union is connected and the tree joining argument below proves (G3). Otherwise $d_\Omega(S_1\cup S_2)$ is either $D_\Omega$ or at most the maximum in the definition of $D_\Omega$; one of $d_\Omega(S_i)$ is $D_\Omega$, so (G3) follows from nonnegativity. In a connected cluster every input support $Y\cap\Omega$ has connected $\hat Y$, and overlap in an $\Omega$-cube keeps the union connected; hence the finite extension never weakens the cluster coefficients actually used below.

(G1) P6's proof of (4.11) (pp. 25–26 [checked]) covers a tree $\Gamma$ by at most $1+M^{-1}|\Gamma|$ cubes of side $(2L+3)M$ such that every
$LM$-cube meeting $\Gamma$ lies in one of them; the cubes of $\mathcal K$ meet $\Gamma$ and their union contains $X\cap\Omega$. Take the infimum.
(G2) A tree of length $\ell M$ meets at most $C_d(\ell+1)$ cubes of $\pi_j$, which form a connected set; $X\cap\Omega$ is contained in the union of
the $\pi'_j$-cubes meeting it, i.e. in its $L$-neighbourhood, and $\square$ lies there. The number of connected sets of $C_d(\ell+1)$ cubes within distance
$L$ of $\square$ is $\le e^{a'(\ell+1)}$, the number of subsets of their $L$-neighbourhoods is $\le2^{(2L+1)^dC_d(\ell+1)}$, and $X$ is determined by
$X\cap\Omega$ and the set of components of $\Omega^c$ it contains, each adjacent to $X\cap\Omega$ (connectedness), at most $3^dn_\pi(X\cap\Omega)$ of
them; by (G1) this gives $\le e^{a_{\rm ent}(\ell+1)}$ sets $X$ with $\ell\le d^{\rm cov}<\ell+1$. Sum over $\ell$. The count for $S$ is the same (the
tree defining $d_\Omega(S)$ lies in $\hat Y(S)$ and meets cubes covering $S$). (G3) The union of the two families covers $(X_1\cup X_2)\cap\Omega$; a
cube $\square\subset X_1\cap X_2\cap\Omega$ lies in a cube $q_i$ of each family (alignment of $\pi'$ with $\pi$), $\Gamma_i$ meets $q_i$, and $q_1\cup q_2$ is
connected of diameter $\le2\sqrt d\,LM\le c_GM$; join $\Gamma_1$, $\Gamma_2$ by a path inside $q_1\cup q_2\subset X_1\cup X_2$ and prune cycles. A component
of $\Omega^c$ is contained in $X_1\cup X_2$ or disjoint from it because this holds for each. For $S_1,S_2$: $\hat Y(S_1\cup S_2)=\hat Y(S_1)\cup\hat Y(S_2)$.
(G4) $Y$ is connected and meets $\Omega$ exactly in $S$; a path in $Y$ from $S$ into $\Omega^c$ stays in one component of $\Omega^c$ until it re-enters
$\Omega$, i.e. $S$ (distinct components of $\Omega^c$ are not adjacent), so $Y\subset\hat Y(S)$; the chosen family of $Y$ covers $S$ and its tree lies
in $Y\subset\hat Y(S)$. (G5) Every point of $X$ lies in a chosen cube (side $LM$) met by $\Gamma$. $\square$

Throughout, $\kappa_0:=\max\{a_{\rm ent}(d,L)+1,\ c_1,\ \kappa_0^{\rm LOC}\}$ with $\kappa_0^{\rm LOC}$ the free parameter of I-5 (LOC §4.4; any value
$\le\frac13\kappa-1$ is allowed there), so a single $\kappa_0=\kappa_0(d,L)$ and $K_0=K_0(d,L)$ serve all entropy sums. Note $c_1\le\kappa_0$.

### 1.3 Inputs used, and the exact form in which each is used

| Key | Statement used | Where proved | Status |
|---|---|---|---|
| I-1 | BG Thm 5.2 (unique small solution, analytic, bounds $K_1$, real global minimiser), Prop 5.1 (perturbed system, $\exists!$, analytic, $\le K_2\delta_1$), Prop 5.4 (linear response $\dot\phi=(G-\Pi)\dot S$) | BG §5; landed `prop51_*`, `lemma53`, `linearResponse` | cited |
| I-2 | BG Thm 6.1 (ii), (iv): $\phi(\mathbb B_j;\Psi)=\phi(\mathbb B'_k;\Psi')|_{\Omega_1}$ for $\Psi=$ `composeField`; Prop 6.4 | BG §6; landed `isEL_compose`, `theorem73_real`, `theorem73_complex`, `prop64` | cited |
| G | GR G-1(b), (d)(1)–(3) (coercivity of the constrained $aL^{-2}Q^*Q+\Delta^{(k)}$), G-4 (Combes–Thomas), G-6(b) (Schur form of $C_x$) | GR §4; landed `constrainedOp`, `constrained_G2v`, `xVariant_constrained_reduction` | cited |
| I-4 | LOC I-4a (both modes), I-4b, I-4c, DG1–DG7 | LOC §3; partly landed (`dg1`–`dg6`, `i4a_*`, `i4b_*`) | abstract pieces PROVED; NC/new cover OPEN |
| I-5 | LOC Theorem I-5 and its proof (AE + GM + DL), variants V2–V5 | LOC §4; landed background-only `i5_background`, `abstract_expansion`, `gm2`, `gm3`, `gm4` | background-only theorem PROVED; fluctuation and modular variants OPEN, VMOD.md |
| I-6 | SF Theorem 2.1; termwise `PremisesTerm`, `SumConds`, `Itw_congr`, `Itw_analytic`, `termwise_irrelevant_all_scales`, `energyW_sub_AW_eq_tsum_IW`, `IW_bound_outside` | SF §2; landed `RenormTermwise*.lean` | abstract termwise results PROVED; actual RG premises to be checked |
| I-7 | SF Theorem 3.2, Lemma 3.1, 3.1′, 3.3 | SF §3; landed abstract `rg_step_infty`, `rg_flow_infty`, `tendsto_rg_solution`, `matrixInfty`, `matrixFree`, `matrixSel` | abstract results PROVED; actual $\nu$-free coefficient and switch OPEN, RGFREE.md |
| PE | PE Theorem PE, PE-L, MY, PE-M | PE §§2–3; landed `pe_xi_eq_exp`, `pe_PY_bound`, `mayer_pe`, `mayer_marked`, `norm_D1_Ff_le` | cited |
| LF | LFR §II.2 (generating sets of a step, $\mathbb B^{\rm loc}$, Lemmas II.2.3, II.2.5, II.2.6), Def II.3.2, II.3.5, II.6.1–II.6.3 | LFR | cited |

### 1.4 The class at step $k$, and the analyticity domain (Finding F-1)

The input is Def-6 (SF §1.3, §1.6) in the whole-lattice case and its subdomain form, the small-field data (D2) of Def-7 together with the boundary
terms (D7) (LFR Definition II.6.2, the restricted functions (1.6)–(1.17) of LFR §II.6.1 = P5 (1.6)–(1.17)). The convention is $\nu$-free at scales
$j\le k_0$ and complete at scales $j>k_0$, with the a priori regime index $k_0:=\max\{k:\beta\nu L^{kd}\le1\}$ (LFR D-IV.11); the free flow
$c_{k+1}=a_{k+1}b_{k+1}$ is used (SF §3.1 ruling), so $a_{k+1}=a_{k+1,u}=aa_k/(a_k+aL^{-2})$ exactly and $d_{k+1}$ does not occur.

**[v2: FL-A11] Amended class input (F-1).** At each scale $j$, require every localized $\mathscr E^{(j)}(y,X;\cdot)$ and $\mathscr M^{(j)}(x,X;\cdot)$ to be analytic on an open neighbourhood of $\Xi^c_j(\mathbb B_j(X);1,\varepsilon_j)$ (for $\mathscr M$, also $\|g\|_{\ell^1}<1$), with the stated bounds on that set. This is the `analyticE` and `analyticM` clause of the landed draft `Balaban/SmallField/Def6.lean` (`IsSF`, through `XiDom`); for subdomains it is the author-accepted amendment to Def-7 (D2) recorded in LFR §II.3.3. The amendment is an **input class** for Theorems 3.1, 5.1 and 5.4. It supersedes SF §1.7 ruling (iv), whose larger data-domain demand is not reproduced by the step. The boundary class (D7) continues to use the H7 domain of LFR Definition II.3.5.

The exact landed inclusions matter. Put $C_0=\mathrm{scaledC0}(d)=8d+12$ and $C_{\Xi1}=\mathrm{xiC1}(d)=(4d+8)(2d+1)$. The landed (Ξ1), `xiC_inPsiTildeC` in `Balaban/SmallField/XiProps.lean`, sends $\Xi^c_j(1,\varepsilon)$ into the complex data domain with radii $C_{\Xi1}\varepsilon$, under $(4d+6)(2d+1)\varepsilon\le1$ and $C_{\Xi1}\varepsilon\le C_1^{\rm BG}$. The landed (Ξ3), `xiC_compose` in `XiComposeField.lean`, sends a scale-$k$ member of $\Xi^c_k(1,\varepsilon)$ under the exact composition (6.2) into $\Xi^c_j(C_0s_{jk},\varepsilon)$; the factor $C_0$ cannot be dropped at $j=k$. The landed background-only `i5_background` in `Balaban/Localization/I5.lean` takes an input $E$ analytic and bounded on
$$\Xi^c_j\bigl(C_0,\ C_0^2\varepsilon'+K_2^{\Xi}\delta_3\bigr),\tag{DL-in}$$
and returns local coefficients analytic on neighbourhoods of $\Xi^c_{k+1}(1,\varepsilon')$, bounded by $E_b e^{-\kappa_0d_j^{\rm cov}(X)-2\kappa\tilde d_{k+1}^{\rm cov}(Y)}$ and local on its landed thickening `thickSet Y`. Its other explicit hypotheses are `BgSetting` (including `ChainNum`), `CovSetup`, `HatConn`, the optimum-tree witness `hopt`, and the rate inequalities in `i5_background`; in particular `ChainNum` includes the $C_{\Xi1}$ smallness and background-domain inequalities. Those hypotheses must be instantiated for the chosen cover. This is a **background-only** theorem; its fluctuation-variable version, the modular version, and their cover hypotheses remain OPEN, with the modular work assigned to notes/phase1/VMOD.md (in preparation).

Here is the required input/output check, including the Cauchy margin. The defining inequalities of $\Xi^c(\sigma,\varepsilon)$ are monotone in $\sigma\varepsilon$ and $\sigma^2\varepsilon$, so (DL-in) is contained in the amended class domain $\Xi^c_j(1,\varepsilon_j)$ if
$$C_0^2(C_0^2\varepsilon'+K_2^{\Xi}\delta_3)<\varepsilon_j.\tag{DL-gap}$$
For all $j\le k$ it suffices to use $\varepsilon'\le\varepsilon_{k+1}$ and prove (DL-gap) with $\varepsilon_j$ replaced by $\varepsilon_k$. Choose $L$ so $L^\alpha>2C_0^4$; then $C_0^4\varepsilon_{k+1}<\varepsilon_k/2$. For the remaining half of the gap, the **landed** `ChainNum.close` hypothesis is
$$N\,\mathrm{composedCloseBound}(d,L,N,m_1,B_G,\kappa,C_{\Xi1}\varepsilon',r_0)\le\delta_3,$$
where `composedCloseBound` (in `Localization/I5Close.lean`) is $10e^{2d\gamma_w}\mathrm{closeConst}(d,L,N,B_G,\kappa,\mathrm{lemma53Const}\,C_{\Xi1}\varepsilon')\exp\{-\gamma_w(r_0-4dL^3)M_1/L\}$, with $M_1=L^{m_1}$. The landed `closeConst` in `DecoupledFieldClose.lean` is exactly linear in its last argument, so this expression equals $K_{\rm close}\varepsilon'\exp\{-\gamma_w(r_0-4dL^3)M_1/L\}$ for a constant $K_{\rm close}$ depending only on the earlier rows. For this sufficient way to make $\delta_3$ small by increasing $M_1$, the cover must supply $r_0^{\rm Lean}>4dL^3$ in these landed units. LFR §I.1.3 row 5a selects $r_0^{\rm Lean}=4dL^3+L$ for the standard cover, giving exactly $e^{-\gamma_wM_1}$ here. At equality the exponential supplies no decay, and at a smaller collar it grows; another argument would then be needed. Admissibility of this collar at the **auxiliary** interface and the remaining `ChainNum` inequalities are OPEN cover inputs, not consequences of `i5_background`. Under those inputs set $\delta_3=N K_{\rm close}\varepsilon'e^{-\gamma_wM_1}$ and choose $M_1$ in row 6 so $C_0^2K_2^{\Xi}N K_{\rm close}e^{-\gamma_wM_1}<1/2$. Since $\varepsilon'\le\varepsilon_k$, this gives $C_0^2K_2^{\Xi}\delta_3<\varepsilon_k/2$ **uniformly in the later choice of $\alpha_0$**. In the fluctuation variant there is an additional perturbation of size $(2K_3+1)\delta_1$ (LOC Lemma DL); the scaled estimate $\delta_1/\varepsilon_k=O(\beta^{-3/8})$ lets the final $\beta_*(\alpha_0,E_0)$ pay it, provided that OPEN variant retains the same strict margin. These inequalities prove (DL-gap) in the stated order. Strictness and `AnalyticOnNhd` of the input give an open neighbourhood of each evaluated closed Cauchy polydisc. The background-only theorem's output is analytic on a neighbourhood of $\Xi^c_{k+1}(1,\varepsilon_{k+1})$ when $\varepsilon'=\varepsilon_{k+1}$. This is the exact input/output radius check; the numerical `ChainNum`, full fluctuation and modular instantiations remain OPEN.

### 1.5 Constants and their order

In the order of the LFR prefix (§I.1.3–§I.1.4, rows as amended there). Rows 0–3: $d\ge3$, $N\ge2$; $\gamma\in(0,\frac12)$, $\alpha=\frac{d-2}2-\gamma$,
$\alpha_1\in(0,\min\{1-2\gamma,\gamma/2\})$ and the auxiliary exponent $\alpha':=\alpha_1/4$ (used only to absorb powers of $p_1(\beta_k)$, Finding
F-4); $L\ge3$ is chosen large enough that $L^\alpha>2(8d+12)^4$ for (DL-gap). Row 4: the $(d,L,N)$-constants $\gamma_0,K_1,K_2,C_3,C_4$ (BG, GR), $c_1,c_G,a_{\rm ent}$ (Lemma 1.2). Row 5: $\kappa_0,K_0$ (§1.2); the class
rate $\kappa:=\kappa_{\rm flow}$, subject to the iteration condition (IC) of §3.7. Row 5a: set $r_0^{\rm Lean}=4dL^3+L$ and choose $m_0$ with $L^{m_0}\ge\max\{14d,L+9,4+r_0^{\rm Lean}/L\}$, as in LFR §I.1.3; then $M/M_1=L^{m_0}$ and the standard cover has $(4L+r_0^{\rm Lean})M_1\le LM$. Row 5b: $\kappa_1\ge\max\{4d(2L+1)^d\kappa,\ 4d\log((2L+1)L^{m_0})+2\}$
(LOC). Row 5′: the I-4 constants $c_*,B_G,c_6,\delta_*,K_3,K_4,c_7,B_4,B_5$ and $B_{\mathbb L}$ (the bound of LOC's $\mathbb L(s)$). Row 6: choose $M_1=L^{m_1}$ sufficiently large that $C_0^2K_2^{\Xi}N K_{\rm close}e^{-\gamma_wM_1}<1/2$ as in §1.4 and for the other stated I-4/I-5 lower bounds, then put $M=L^{m_0}M_1$; `ChainNum.close` holds with $\delta_3=N K_{\rm close}\varepsilon'e^{-\gamma_wM_1}$. This choice precedes $\alpha_0$ because the required ratio has no $\varepsilon'$ in it. The standard-cover margin is numerical; verifying the **auxiliary** interface with that collar is OPEN in Lemma 2.8. The older LOC integer cube collar $r_0^{\rm LOC}=8$ uses different units. Row 6b:
$K_5:=9K_0(16dK_1LM)^2((2L+3)M)^d$ (P4 (5.24) with (G1), (G5)), $B_6:=NL^dB_{\mathbb L}+2$, and the constants $C_U,C_{\rm PE},C_4',C_5,C_6$ defined below.
**[v2.1: Lemma 2.5]** Enlarge the earlier upper-bound constants to $K_2,B_5\ge1$ before row 9. The adopted cutoff functions have $p_j(\beta_k)=A_j\ell_k^{p_0}$ for $j=0,1$ with a common logarithmic argument $\ell_k$ (LFR §I.1.3, row 8); here $\ell_k=\log\beta_k$ in the normalization of (1.1). Hence in row 9 choose $p_1(\beta_k)/p_0(\beta_k)=A_1/A_0\le(3B_5K_2)^{-1}$. LFR's $A_0=4K_2B_5A_1$ gives the stricter ratio $1/(4K_2B_5)$. In row 16 also require $B_5\beta_k^{-1/2}p_1(\beta_k)\le\frac12C_3c_7$ for every admitted $k$, as needed in Lemma 2.5; since $\beta_k^{-1/2}p_1(\beta_k)$ eventually decreases and $\beta_k\ge\beta/2$, one final lower bound on $\beta$ suffices.
Rows 10–11: $c_8$, a fixed $0<\alpha_0\le\alpha_0^*$ (all $\varepsilon_j=\alpha_0(1+\sum_{n\ge j}n^{-2})L^{-j\alpha}$ for $j\ge1$, with $\varepsilon_0:=\alpha_0(1+\sum_{n\ge1}n^{-2})$), then a fixed $E_0\ge E_0^*:=400C_4'B_6K_0K_5$ (§5.2, Step 8), $c_9:=\beta^{-1/4}$ (P4 (5.40)); last $\beta$
(row 16). **[v2: FL-A10]** The final threshold is $\beta_*(\alpha_0,E_0)$: it must enforce $168C_5E_0B_6K_5\alpha_0^{-2}\beta^{-1}\le1$ and therefore cannot be uniform as $\alpha_0\downarrow0$ or $E_0\uparrow\infty$. The late geometric thresholds $\lambda_*$ in (Λ28′) and $\lambda_*^{\rm old}$ in (3.14) are chosen after the same earlier constants and included in row 16. Every "for $\beta$ large" below has this quantifier order.

Two elementary consequences of (H.6) used repeatedly ($\gamma_k\in[\frac12,2]$): $\beta_k^{-1/2}\le2\beta^{-1/2}\eta^{\frac{d-2}2}$, and for every $\alpha'>0$
$$p_n(\beta_k)=A_n(\log\beta_k)^{p_n}\le C_{\alpha'}\,\beta^{\alpha'}\eta^{-\alpha'}\qquad(n=0,1),\tag{1.1}$$
because $(\log x)^{p}\le C x^{\alpha'/(d-2)}$ and $\beta_k\le2\beta\eta^{-(d-2)}$; hence $\beta_k^{-1/2}\varepsilon_k^{-1}\le2\alpha_0^{-1}\beta^{-1/2}\eta^{\gamma}$.

---
## 2. The step at $\lambda=\infty$ precisely

### 2.1 The operators

**Definition 2.1 (one renormalization transformation; P4 (2.1), P1 (1.11), LFR Definition II.5.6).** For $\vartheta,w\in\mathbb C^N$ let
$$t_k(\vartheta,w):=\Big(\frac{\beta_kaL^{d-2}}{2\pi}\Big)^{N/2}\exp\Big(-\frac{\beta_kaL^{d-2}}2\,(\vartheta-w)\cdot(\vartheta-w)\Big),$$
so that $\int_{\mathbb R^N}t_k(\vartheta,w)\,d\vartheta=1$. For a density $\rho$ of $\psi=\psi_k$ on $T^{(k)}_1$ and a block field $\theta$ on $T^{(k+1)}_L$,
$$(T^{(k)}\rho)(\theta):=\int\prod_{z\in T^{(k+1)}_L}t_k\big(\theta(z),(Q\psi)(z)\big)\,\rho(\psi)\,d\psi ,\qquad (Q\psi)(z)=L^{-d}\sum_{x\in B_{k+1}(z)}\psi(x).$$
$S^{(k)}$ is the passage to scale-$(k+1)$ units ($T_\eta\to T_{L^{-1}\eta}$, $T^{(k+1)}_L\to T^{(k+1)}_1$; spins unchanged; P4 §3). With the field renormalization
$z_{k+1}=1+\zeta_{k+1}$ the new density is $\rho_{k+1}(\psi_{k+1}):=z_{k+1}^{N|T^{(k+1)}_1|}(S^{(k)}T^{(k)}\rho)(z_{k+1}\psi_{k+1})$, so
$\int\rho_{k+1}\,d\psi_{k+1}=\int\rho\,d\psi$ (Fubini and $\int t_k\,d\vartheta=1$). The *small-field part* of the step is $\chi_{k+1}S^{(k)}T^{(k)}\chi^{(k)}$ with
$\chi^{(k)}=\chi_{(2.2)}\,\chi_{\rm fl}$, $\chi_{(2.2)}=\mathbf 1[|\theta-Q\psi|<2\delta_k\text{ on every block}]$, $\delta_k:=\beta_k^{-1/2}p_0(\beta_k)$, and $\chi_{\rm fl}$ the
restriction of the fluctuation variables of Lemma 2.5 (P4 (2.2), (2.40)).

The input on the whole lattice (Def-6, (H.1)) is
$\rho_k=\chi_k\exp[-\beta_kA^\star_k(\psi,\phi_k(\psi))+\mathscr E_k(\psi)-E_k|T^{(k)}_1|+\mathscr F_k(\psi,g)]$ where, in the **complete** convention ($k>k_0$),
$$A_k(\psi,\phi)=\tfrac{a_k}2\|\psi-Q_k\phi\|^2+\tfrac12\|\partial^\eta\phi\|^2_\eta+\tfrac{\nu_k}2\|\phi-h\|^2_\eta,\qquad \phi_k(\psi)=\text{the small solution of (EL) for }A_k,$$
and in the **$\nu$-free** convention ($k\le k_0$, P5 (1.9)) $\phi_k=\phi^0_k(\psi)$ is the small solution for $A^0_k:=A_k|_{\nu_k=0}$ while the action keeps the
$\nu$-term: $A^\star_k(\psi,\phi^0_k)=A^0_k(\psi,\phi^0_k)+\frac{\nu_k}2\|\phi^0_k-h\|^2_\eta$ (P5 p. 490: "we keep it in the main action"). At $\lambda=\infty$ the
constraint is $\phi\cdot\phi=1$ with multiplier $\alpha$ (BG (EL)); for real data $\phi_k(\psi)$ is the unique global minimiser over $(S^{N-1})^{T_\eta}$ (BG Thm 5.2 (4)).

### 2.2 The critical point and the Gaussian composition

Let $J_k(\theta,\psi):=\frac12aL^{-2}\|\theta-Q\psi\|_L^2+A^0_k(\psi,\phi_k(\psi))+\iota\frac{\nu_k}2\|\phi_k(\psi)-h\|^2_\eta$, with $\iota=1$ in both conventions but $\phi_k$ the
complete resp. $\nu$-free background. Put $A^\eta_{k+1}(\theta,\phi):=\frac12a_{k+1}L^{-2}\|\theta-Q_{k+1}\phi\|_L^2+\frac12\|\partial^\eta\phi\|^2_\eta+\frac{\nu_k}2\|\phi-h\|^2_\eta$, the
action of scale $k+1$ written on the $\eta$-scale (P4 (2.11)–(2.12), (3.1)), and let $\phi_{k+1}(\theta)$, $\alpha_{k+1}(\theta)$ be its background (with $\nu_k$ in the
variational problem in the complete convention, without in the $\nu$-free one).

**Lemma 2.2 (critical point; P4 (2.4)–(2.14) at $\lambda=\infty$; proved).** Let $a_{k+1}:=aa_k/(a_k+aL^{-2})$ (P4 (2.9)).
(a) *(Gaussian composition.)* For every $\phi$, $\min_\psi\big[\frac12aL^{-2}\|\theta-Q\psi\|_L^2+\frac{a_k}2\|\psi-Q_k\phi\|^2\big]=\frac12a_{k+1}L^{-2}\|\theta-Q_{k+1}\phi\|_L^2$, attained exactly at
$$\Psi(\theta,\phi):=Q_k\phi+\frac{a_{k+1}}{a_k}L^{-2}Q^*(\theta-Q_{k+1}\phi).\tag{2.1}$$
(b) *(Complete convention, real data.)* For real $(\theta,h)$ with $\theta$ in the domain of $\phi_{k+1}$ (e.g. $(\theta,h)\in\tilde\Psi_{k+1}(4L\beta_k^{-1/2}p_0(\beta_k))$, P4 (2.3)),
$\psi^{(k)}(\theta):=\Psi(\theta,\phi_{k+1}(\theta))$ is the **unique global minimiser** of $\psi\mapsto J_k(\theta,\psi)$, $J_k(\theta,\psi^{(k)}(\theta))=A^\eta_{k+1}(\theta,\phi_{k+1}(\theta))$, and
$$\phi_k(\psi^{(k)}(\theta))=\phi_{k+1}(\theta),\qquad\alpha_k(\psi^{(k)}(\theta))=\alpha_{k+1}(\theta).\tag{2.2}$$
(c) *(Complex data.)* For complex $(\theta,h)$ in $\tilde\Psi^c_{k+1}(\delta,\varepsilon)$ with $\delta,\varepsilon$ as in BG Thm 5.2 and $4dK_1\delta\le\varepsilon$, (2.1) with the complex
small solution satisfies (2.2) (both sides being small solutions).
(d) *($\nu$-free convention.)* (a)–(c) hold verbatim for $J^0_k:=J_k|_{\iota=0}$ and the $\nu$-free backgrounds; $\psi^{(k)}$ is a critical point of $J^0_k$, not of $J_k$.

*Proof.* (a) With $Q^*$ the lift (adjoint of $Q$ for $\|\cdot\|_L$, $\|\cdot\|$), $QQ^*=1$ and $P:=Q^*Q$ the block projection, the gradient equation is
$(a_k+aL^{-2}P)\psi=a_kQ_k\phi+aL^{-2}Q^*\theta$. Its $(1-P)$-part gives $(1-P)\psi=(1-P)Q_k\phi$, its $P$-part $P\psi=\frac{a_k}{a_k+aL^{-2}}Q^*Q_{k+1}\phi+\frac{aL^{-2}}{a_k+aL^{-2}}Q^*\theta$
($PQ_k=Q^*Q_{k+1}$), whence (2.1) since $\frac{aL^{-2}}{a_k+aL^{-2}}=\frac{a_{k+1}}{a_k}L^{-2}$. With $w=\theta-Q_{k+1}\phi$ and $c=a_k+aL^{-2}$: $\theta-Q\Psi=\frac{a_k}cw$, $\Psi-Q_k\phi=\frac{aL^{-2}}cQ^*w$,
$\|Q^*w\|^2=\|w\|_L^2$, so the minimum is $\frac12\|w\|_L^2\frac{aL^{-2}a_k}{c^2}(a_k+aL^{-2})=\frac12a_{k+1}L^{-2}\|w\|_L^2$; the function is strictly convex in $\psi$.
(b) $J_k(\theta,\psi)=\min_{|\phi|=1}\big[\frac12aL^{-2}\|\theta-Q\psi\|_L^2+A_k(\psi,\phi)\big]$ for real data (definition of $\phi_k$ as global minimiser). Exchanging the two infima
and using (a), $\inf_\psi J_k=\min_{|\phi|=1}A^\eta_{k+1}(\theta,\phi)=A^\eta_{k+1}(\theta,\phi_{k+1})$ (BG Thm 5.2 (4) for the single-scale generating set of level $k+1$).
The pair $(\psi^{(k)},\phi_{k+1})$ attains it. If $\psi_*$ is any minimiser and $\phi_*$ a minimiser of $A_k(\psi_*,\cdot)$, then $(\psi_*,\phi_*)$ is a joint minimiser,
so $\phi_*$ minimises $A^\eta_{k+1}(\theta,\cdot)$, hence $\phi_*=\phi_{k+1}$ (uniqueness), and $\psi_*=\Psi(\theta,\phi_*)$ by strict convexity; so $\psi_*=\psi^{(k)}$ and
$\phi_k(\psi^{(k)})=\phi_{k+1}$. The multipliers agree because $\alpha=-\phi\cdot(H_D(0)\phi-S)$ (BG §1.2) is a function of $\phi$ and the data. (c) (2.1) is BG (6.2)
for the pair (single-scale level $k$) $\prec$ (single-scale level $k+1$) with $n=k$, $p=k+1$; BG Thm 6.1 (ii), (iv) (landed `isEL_compose`,
`theorem73_complex`) gives (2.2) for complex data. (d) The $\nu$-term is not part of the variational problems; (a)–(c) do not use it. $\square$

*Remark.* P4 obtains the unique critical point in $\tilde\Psi_k(L^{-2}c_1)$ from P2 Prop 4.1; for hard spins (b) is a global statement and needs only BG Thm 5.2 (4).

### 2.3 The exact expansion around the critical point

Let $\psi=\psi^{(k)}(\theta)+\psi'$ with $(\psi,h)$ in the domain of the small solution, $\phi':=\phi_k(\psi)-\phi_{k+1}(\theta)$, $\alpha':=\alpha_k(\psi)-\alpha_{k+1}(\theta)$,
and $H_k:=-\Delta^\eta+a_kQ_k^*Q_k+\mu_k+\alpha_{k+1}$ ($\mu_k=\nu_k$ complete, $0$ $\nu$-free), $G_k:=H_k^{-1}$, $\Pi_k:=$ `constrainedOp` $(G_k,\phi_{k+1})
=G_k\phi_{k+1}[\phi_{k+1}\cdot G_k\phi_{k+1}]^{-1}\phi_{k+1}\cdot G_k$ (GR (1.8′)). Let $(\phi^{(1)},\alpha^{(1)})$ be the linear response to the data tangent $a_kQ_k^*\psi'$
(BG Prop 5.4): $\phi^{(1)}=(G_k-\Pi_k)a_kQ_k^*\psi'$, $\alpha^{(1)}=[\phi_{k+1}\cdot G_k\phi_{k+1}]^{-1}\phi_{k+1}\cdot G_ka_kQ_k^*\psi'$, and $\phi_2:=\phi'-\phi^{(1)}$.

**Lemma 2.3 (exact expansion; P4 (2.15)–(2.27), P5 (2.23)–(2.30) at $\lambda=\infty$; proved).**
(a) *(Chord identity.)* In the complete convention
$$J_k(\theta,\psi)=A^\eta_{k+1}(\theta,\phi_{k+1})+\tfrac12aL^{-2}\|Q\psi'\|_L^2+\tfrac{a_k}2\|\psi'-Q_k\phi'\|^2+\tfrac12\langle\phi',(-\Delta^\eta+\mu_k+\alpha_{k+1})\phi'\rangle_\eta .\tag{2.3}$$
(b) *(Quadratic part and interaction.)* $J_k(\theta,\psi)=A^\eta_{k+1}(\theta,\phi_{k+1})+\frac12aL^{-2}\|Q\psi'\|_L^2+\frac12\langle\psi',\Delta^{(k)}\psi'\rangle+V^{(k)}(\psi')$ with
$$\Delta^{(k)}:=a_k-a_k^2Q_k(G_k-\Pi_k)Q_k^*,\qquad V^{(k)}(\psi'):=\tfrac12\langle\alpha^{(1)},\phi'\cdot\phi'\rangle_\eta+\tfrac12\langle\phi_2,H_k\phi_2\rangle_\eta .\tag{2.4}$$
(c) *($\nu$-free convention.)* With the $\nu$-free objects ($\mu_k=0$ in $H_k$), $J_k=J^0_k+\frac{\nu_k}2\|\phi_k(\psi)-h\|^2_\eta$ satisfies
$J_k(\theta,\psi)=A^\star_{k+1}(\theta,\phi^0_{k+1})+\frac12aL^{-2}\|Q\psi'\|_L^2+\frac12\langle\psi',\Delta^{(k)}\psi'\rangle+V^{(k)}(\psi')+V^{(k)}_\nu(\psi')$, where
$A^\star_{k+1}=A^\eta_{k+1}|_{\nu\text{-free }\phi}$ (the $\nu$-term evaluated at the $\nu$-free background) and $V^{(k)}_\nu(\psi'):=\nu_k\langle\phi',\phi^0_{k+1}-h\rangle_\eta+\frac{\nu_k}2\|\phi'\|_\eta^2$.
(d) *(Bounds, locality.)* For $|\psi'|\le\delta'\le\frac12C_3c_7$ (P6 (4.4)): $\|\phi'\|_*+|\alpha'|_2\le K_2|\psi'|$, the same for $\phi^{(1)},\alpha^{(1)}$, and
$\|\phi_2\|_*+|\alpha'-\alpha^{(1)}|_2\le2K_2(C_3c_7)^{-1}|\psi'|^2$; hence $V^{(k)}=\sum_{z\in T^{(k+1)}_L}V^{(k)}(z)$ (all scalar products restricted to $B_{k+1}(z)$; P4
(2.28)) with $|V^{(k)}(z;\psi')|\le C_VL^d|\psi'|^3$, $C_V:=9K_2^2(C_3c_7)^{-1}$; $V^{(k)}(z)$ is analytic in $(\psi',\phi_{k+1},\alpha_{k+1})$, $O(N)$-invariant and Euclid-covariant
(P4 (2.29)–(2.30)).

*Proof.* (a) Expand $\frac12aL^{-2}\|\theta-Q\psi^{(k)}-Q\psi'\|_L^2+A_k(\psi^{(k)}+\psi',\phi_{k+1}+\phi')$. The zeroth order is $A^\eta_{k+1}(\theta,\phi_{k+1})$ (Lemma 2.2 (a)). The
term linear in $\psi'$ is $\langle-aL^{-2}Q^*(\theta-Q\psi^{(k)})+a_k(\psi^{(k)}-Q_k\phi_{k+1}),\psi'\rangle=0$ (the $\psi$-equation, P4 (2.7)). The term linear in $\phi'$ is
$\langle a_kQ_k^*(Q_k\phi_{k+1}-\psi^{(k)})-\Delta^\eta\phi_{k+1}+\mu_k(\phi_{k+1}-h),\phi'\rangle_\eta=-\langle\alpha_{k+1}\phi_{k+1},\phi'\rangle_\eta$ by (EL) at $\lambda=\infty$, and the constraint
$(\phi_{k+1}+\phi')\cdot(\phi_{k+1}+\phi')=1=\phi_{k+1}\cdot\phi_{k+1}$ gives $\phi_{k+1}\cdot\phi'=-\frac12\phi'\cdot\phi'$ pointwise (bilinear, valid for complex data), so this term is
$\frac12\langle\alpha_{k+1},\phi'\cdot\phi'\rangle_\eta$. The quadratic terms are the rest of (2.3). (b) Write $\phi'=\phi^{(1)}+\phi_2$ in
$\frac{a_k}2\|\psi'\|^2-a_k\langle\psi',Q_k\phi'\rangle+\frac12\langle\phi',H_k\phi'\rangle_\eta$ (this is the sum of the last two terms of (2.3), $H_k$ containing $a_kQ_k^*Q_k$). The
$\phi^{(1)}$-$\phi^{(1)}$ part is $\frac12\langle\psi',\Delta^{(k)}\psi'\rangle$ because $(G_k-\Pi_k)H_k(G_k-\Pi_k)=G_k-\Pi_k$ ($\Pi_kH_k\Pi_k=\Pi_k=G_kH_k\Pi_k=\Pi_kH_kG_k$). The cross part is
$\langle H_k\phi^{(1)}-a_kQ_k^*\psi',\phi_2\rangle_\eta=-\langle\alpha^{(1)}\phi_{k+1},\phi_2\rangle_\eta$ (linearised (EL): $H_k\phi^{(1)}+\alpha^{(1)}\phi_{k+1}=a_kQ_k^*\psi'$, $\phi_{k+1}\cdot\phi^{(1)}=0$), and
$\phi_{k+1}\cdot\phi_2=\phi_{k+1}\cdot\phi'=-\frac12\phi'\cdot\phi'$. (c) Add $\frac{\nu_k}2\|\phi^0_{k+1}+\phi'-h\|^2_\eta=\frac{\nu_k}2\|\phi^0_{k+1}-h\|^2_\eta+\nu_k\langle\phi',\phi^0_{k+1}-h\rangle_\eta+\frac{\nu_k}2\|\phi'\|^2_\eta$ to (b) for the
$\nu$-free objects. (d) $\phi'$ is the solution of BG Prop 5.1 (perturbed system with $\delta\Psi=\psi'$ lifted, $\phi_0=\phi_{k+1}$, $\alpha_0=\alpha_{k+1}$, $f_1=0$, $g=0$; mode U of LOC
I-4a), analytic in $\psi'$ with the bound $K_2|\psi'|$ (P4 (2.18)); $\phi^{(1)}$ is its derivative at $0$, and $\phi_2$ the second-order Taylor remainder, bounded by Cauchy on
the circle $|\tau|=C_3c_7/(2|\psi'|)$ exactly as P6 (4.4). (2.4) is a sum of products of local quantities over sites and bonds of $T_\eta$ and blocks of $T^{(k)}_1$. Invariance:
the backgrounds are equivariant (uniqueness). $\square$

*Remarks.* (i) (2.4) is P4 (2.27) at $1/\lambda=0$, simplified by the linearised equation: P4's two cross terms combine into $\frac12\langle\alpha^{(1)},\phi'\cdot\phi'\rangle$. (ii)
**Design choice D-FL.1.** P5 (2.29) puts $\frac{\nu_k}2\|\phi^{(1)}\|^2$ into the quadratic form in the $\nu$-free convention; we keep the covariance equal to the one of
LOC I-4c (no $\nu$) and put the whole $\nu$-variation into $V^{(k)}_\nu$. For $k\le k_0$ ($\beta_k\nu_k\le e^{2\epsilon}$) this term is $O(\beta_k^{-1}p_1^2)$ per unit site after the
substitution (2.7), smaller than the cubic interaction; the fluctuation integral is the same, only its Gaussian part is split differently.

### 2.4 The covariance

**Lemma 2.4 (covariance; cited from GR, LOC, with the identification proved).** Let $(\phi_{k+1},\alpha_{k+1})$ be the background of real data in the domain of
Lemma 2.5, or of complex data within distance $\epsilon\le\epsilon_*(d,L)$ in the norms of GR G-1(d).
(a) $\mathrm{Re}\,(aL^{-2}Q^*Q+\Delta^{(k)})\ge\frac12\gamma_0'L^{-2}$ (GR G-1(b), (d)(1)–(2): P4 (2.24)–(2.25); for real data $Q_k\Pi_kQ_k^*\succeq0$, the constrained form dominates the
unconstrained one).
(b) $C^{(k)}:=(aL^{-2}Q^*Q+\Delta^{(k)})^{-1}$ exists on $\ell^2(T^{(k)}_1;\mathbb C^N)$ and $|C^{(k)}(x,x')|\le4\gamma_0'^{-1}L^2e^{-\mu_0|x-x'|}$ (GR G-4(a) with the entry decay
GR G-1(d)(3), G-2(i)).
(c) $C^{(k)1/2}:=\frac1\pi\int_0^\infty x^{-1/2}(aL^{-2}Q^*Q+\Delta^{(k)}+x)^{-1}dx$ is the principal square root, $\|C^{(k)1/2}\|_{\ell^2\to\ell^2},\|C^{(k)1/2}\|_{\ell^\infty\to\ell^\infty}\le B_5$, and
$\frac12\log\det C^{(k)}=-\frac12\sum_{y}\mathrm{tr}\,\mathbb L(y,y)$, $\mathbb L:=\log(aL^{-2}Q^*Q+\Delta^{(k)})$ (P4 (2.58)).
(d) $(aL^{-2}Q^*Q+\Delta^{(k)}+x)^{-1}=A_{k,x}+a_k^2A_{k,x}Q_k(G_{k,x}-\Pi_{k,x})Q_k^*A_{k,x}$ with $A_{k,x}=(a_k+x+aL^{-2}Q^*Q)^{-1}$ and $G_{k,x},\Pi_{k,x}$ of GR (1.7) (GR G-6(b),
LOC I-4c (iv); landed `xVariant_constrained_reduction`), so $C^{(k)},C^{(k)1/2},\mathbb L$ are the values at $s=1$ of LOC's decoupled $C_x(s)$, $C^{(k)1/2}(s)$, $\mathbb L(s)$.

*Proof.* (a)–(b): the cited statements. (c) For the sup bound: the kernel of $(A+x)^{-1}$ decays like $\frac2{\gamma_0'L^{-2}+x}e^{-\mu_0|x_1-x_2|}$ uniformly in $x\ge0$ (GR G-4(a)
with $t=x$), and $\int_0^\infty x^{-1/2}(\frac12\gamma_0'L^{-2}+x)^{-1}dx<\infty$, so the kernel of $C^{1/2}$ is summable uniformly; the $\ell^2$ bound is LOC I-4c (ii); the
square-root and logarithm identities are LOC I-4c (iv) (functional calculus for an operator with spectrum in $\{\mathrm{Re}\,z>c\}$). (d) cited. $\square$

The sup-norm bound in (c) is what P4 (2.39) uses ("the operator $C^{(k)1/2}$ is bounded, e.g. by a constant $B_5$"); LOC I-4c (ii) states only the $\ell^2$ bound
(minor addition, Finding F-5 in §6.2).

### 2.5 The characteristic functions and the product measure

**Lemma 2.5 (only $\chi_{\rm fl}$ remains; P4 (2.31), (2.39)–(2.40) at $\lambda=\infty$; [v2.1] proved with the separate margins below).** Let $\chi_{k+1,u}(\theta)$ be the indicator of
$$|\theta-Q_{k+1}\phi_{k+1}|<\tfrac32\delta_k,\quad|\partial^\eta\phi_{k+1}|,\ |\Delta^\eta\phi_{k+1}|,\ |\alpha_{k+1}|<\tfrac12\delta_k,\quad\big[\text{complete only: }|\phi_{k+1}-h|<\tfrac12\nu_k^{-1/2}\delta_k\big],$$
and suppose $K_2,B_5\ge1$ (enlarge these upper-bound constants if needed), $0<\nu_k\le1$ in the complete convention, and $p_1(\beta_k)/p_0(\beta_k)\le(3B_5K_2)^{-1}$ (P4 (2.40)). Take $\beta$ large enough that $B_5\beta_k^{-1/2}p_1(\beta_k)\le\frac12C_3c_7$, the radius of Lemma 2.3(d). On $\{\chi_{k+1,u}=1\}$, for $\psi=\psi^{(k)}(\theta)+\beta_k^{-1/2}C^{(k)1/2}\hat\psi$ with $\hat\psi$ real,
$$\chi_k(\psi)\,\chi_{(2.2)}(\theta,\psi)\,\chi_{\rm fl}(\hat\psi)=\chi_{\rm fl}(\hat\psi),\qquad\chi_{\rm fl}(\hat\psi):=\prod_{x\in T^{(k)}_1}\mathbf 1[|\hat\psi(x)|<p_1(\beta_k)].$$
*Proof.* Set $t:=B_5\beta_k^{-1/2}p_1(\beta_k)\le\delta_k/(3K_2)$ and $u:=K_2t\le\delta_k/3$. On $|\hat\psi|<p_1$, Lemma 2.4(c) gives $|\psi'|<t$ and Lemma 2.3(d) gives changes of the background, its scaled first differences and Laplacian, and its multiplier of at most $u$. The assumed radius lets us apply that lemma. At $\hat\psi=0$, (2.2) identifies $\phi_k(\psi^{(k)})=\phi_{k+1}$ and $\alpha_k=\alpha_{k+1}$. The inequalities must be checked with their **individual** thresholds:

- For $\chi_k$'s field mismatch, (2.1) and $a_{k+1}/a_k\le1$ give $|\psi^{(k)}-Q_k\phi_{k+1}|<\frac32L^{-2}\delta_k$. After the fluctuation its size is $<\frac32L^{-2}\delta_k+t+u\le(\frac32L^{-2}+\frac23)\delta_k\le\frac56\delta_k<\delta_k$ for $L\ge3$.
- The first-difference, Laplacian, and multiplier tests of $\chi_k$ start below $\delta_k/2$ by the definition of $\chi_{k+1,u}$; after the change each is below $\delta_k/2+u\le5\delta_k/6<\delta_k$. In the complete convention the mass test similarly satisfies $|\phi_k-h|<\nu_k^{-1/2}\delta_k/2+u\le5\nu_k^{-1/2}\delta_k/6$, since $\nu_k\le1$. There is no mass test in the $\nu$-free convention.
- The separate indicator $\chi_{(2.2)}$ tests $|\theta-Q\psi|<2\delta_k$. At zero fluctuation, (2.1) gives $|\theta-Q\psi^{(k)}|<3\delta_k/2$. The change is at most $|Q\psi'|<t\le\delta_k/3$, so the result is $<11\delta_k/6<2\delta_k$.

Thus every factor other than $\chi_{\rm fl}$ equals one on its support. The P4 (2.40) ratio suffices; the invalid combined comparison $3/4+1/3<1$ is not used. $\square$

The fluctuation measure is therefore the **product of probability measures**
$$\nu_{p_1}:=\bigotimes_{x}\nu_{1},\qquad\nu_1(d\hat\psi)=Z_1^{-1}\mathbf 1[|\hat\psi|<p_1(\beta_k)]e^{-\frac12|\hat\psi|^2}d\hat\psi,\qquad\log\big((2\pi)^{-N/2}Z_1\big)=e(N,p_1)=O(e^{-\frac14p_1^2})\tag{2.5}$$
(P5 (3.13)). This settles ER-101 for the small-field fluctuation integral: $\chi_{\rm fl}$ is a product of site indicators by definition (P4 (2.40), P5 (2.42)).

### 2.6 The fluctuation integral and the new contributions (whole lattice)

**Proposition 2.6 (P4 (2.36)–(2.63) at $\lambda=\infty$; proved, algebra).** On $\{\chi_{k+1,u}=1\}$, in the complete convention,
$$\chi_{k+1,u}(T^{(k)}\chi^{(k)}\rho_k)(\theta)=\chi_{k+1,u}\exp\Big[-\beta_kA^\eta_{k+1}(\theta,\phi_{k+1})+\mathscr E_k(\psi^{(k)}(\theta))-E'''_k|T^{(k)}_1|+\mathscr F_k(\psi^{(k)}(\theta),g)+\mathscr E_0^{(k+1)}(\theta)+\mathscr F_0^{(k+1)}(\theta,g)\Big],\tag{2.6}$$
where, with the substitution $\psi'=\beta_k^{-1/2}C^{(k)1/2}\hat\psi$ (2.7) and the measures ($s,t\in[0,1]$)
$$d\mu_{s,t}(\hat\psi):=Z_{s,t}^{-1}\,d\nu_{p_1}(\hat\psi)\exp\big[-\beta_kV^{(k)}(\beta_k^{-1/2}C^{(k)1/2}s\hat\psi)+\delta\mathscr E_k(\beta_k^{-1/2}C^{(k)1/2}s\hat\psi)+\delta\mathscr F_k(\beta_k^{-1/2}C^{(k)1/2}t\hat\psi,g)\big],$$
$\delta\mathscr E_k(\psi'):=\mathscr E_k(\psi^{(k)}+\psi')-\mathscr E_k(\psi^{(k)})$, $\delta\mathscr F_k$ likewise,
$$\mathscr E_0^{(k+1)}=\tfrac12\log\det C^{(k)}+\mathscr E_1^{(k+1)},\qquad\mathscr E_1^{(k+1)}=\int_0^1\!ds\int d\mu_{s,0}\Big(-\beta_k^{1/2}\big\langle V^{(k)\prime}(\beta_k^{-1/2}C^{1/2}s\hat\psi),C^{1/2}\hat\psi\big\rangle+\beta_k^{-1/2}\big\langle\delta\mathscr E_k'(\cdot),C^{1/2}\hat\psi\big\rangle\Big),\tag{2.8}$$
$$\mathscr F_0^{(k+1)}(g)=\langle g,\beta_k^{-1/2}\mathscr M_0^{(k+1)}(g)\rangle_1=\int_0^1\!dt\int d\mu_{1,t}\,\tfrac d{dt}\delta\mathscr F_k(\beta_k^{-1/2}C^{(k)1/2}t\hat\psi,g),\tag{2.9}$$
$E''_k=E'_k+\frac12N\log\beta_k$, $E'_k=E_k-\frac12L^{-d}N\log(\beta_kaL^{-2}/2\pi)$, $E'''_k=E''_k-e(N,p_1)-\frac N2\log2\pi$ (P4's volume element on $T^{(k+1)}_L$ carries the weight $L^d$ per block, which accounts for the difference between P4's $\log(\beta_kaL^{-2})$ and the normalization of $t_k$; only vacuum constants are affected); the localized forms are P4 (2.56)–(2.60):
$\mathscr E_0^{(k+1)}=\sum_{z\in T^{(k+1)}_L}\mathscr E_0^{(k+1)}(z)$, $\mathscr E_0^{(k+1)}(z)=-\frac12\sum_{y\in B(z)}\mathrm{tr}\,\mathbb L(y,y)+\mathscr E_1^{(k+1)}(z)$, $\mathscr E_1^{(k+1)}(z)$ the same formula with
the scalar products restricted to $y\in B_{k+1}(z)$; $\mathscr M_0^{(k+1)}(x;g)$ is (2.53) of P4. The objects are Euclid-covariant and $O(N)$-invariant
(resp. equivariant) (P4 (2.61)–(2.62)). In the $\nu$-free convention replace $A^\eta_{k+1}$ by $A^\star_{k+1}$ and $V^{(k)}$ by $V^{(k)}+V^{(k)}_\nu$.

*Proof.* Insert $\rho_k$ into Definition 2.1; extract $\exp[-\frac12N L^{-d}\log(2\pi/\beta_kaL^{-2})|T^{(k)}_1|]$ from $\prod t_k$ (this is $E'_k$); substitute $\psi=\psi^{(k)}(\theta)+\psi'$
(Lemma 2.3 (b)); the exponent becomes $-\beta_kA^\eta_{k+1}+\mathscr E_k(\psi^{(k)})+\mathscr F_k(\psi^{(k)})$ plus $-\frac{\beta_k}2\langle\psi',(aL^{-2}Q^*Q+\Delta^{(k)})\psi'\rangle-\beta_kV^{(k)}(\psi')
+\delta\mathscr E_k(\psi')+\delta\mathscr F_k(\psi')$. Change variables
$$\psi'=\beta_k^{-1/2}C^{(k)1/2}\hat\psi\qquad(d\psi'=\beta_k^{-N|T^{(k)}_1|/2}\det C^{(k)1/2}\,d\hat\psi)\tag{2.7}$$
and use Lemma 2.5. The integral over $\hat\psi$ is $Z_{1,1}$; $\log Z_{1,1}-\log Z_{0,0}=\int_0^1\partial_s\log Z_{s,0}\,ds+\int_0^1\partial_t\log Z_{1,t}\,dt$, and
$\partial_s\log Z_{s,0}=\langle\partial_s(\text{exponent})\rangle_{s,0}$, which is the integrand of (2.8) ($V^{(k)}$ is differentiated along $s\hat\psi$); $Z_{0,0}=((2\pi)^{N/2}e^{e(N,p_1)})^{|T^{(k)}_1|}$. For real
$(\theta,h)$ all $Z_{s,t}>0$; for complex arguments $Z_{s,t}\ne0$ and the logarithms are the analytic ones given by the cluster expansion (Theorem 3.4, PE (a), (e)), which
agree with the real ones on real arguments. $\square$

### 2.7 The subdomain form: the step on $\Omega_{k+1}$ (P5 §§2–3)

On a representation (LFR Definition II.6.1) the step is P5 (2.1)–(3.18). We list each object, its definition, and what changes at $\lambda=\infty$; the algebra
is P5's (checked on the text layer, pp. 501–521) with the changes of §§2.2–2.6. **Status: cited (P5), with the $\lambda=\infty$ changes proved by the lemmas above.**

| Object | Definition (source) | $\lambda=\infty$ / this document |
|---|---|---|
| Domains | $U_k=Z_k^\approx$, $W_k=(Z^c_k)^{\approx2}$, $\Omega'_{k+1}$ (2.3), $\mathsf P_{k+1}$ (2.6), $\Omega_{k+1}$ (2.8), $\mathsf Q_{k+1}$ (2.14), $\mathsf R_{k+1}$ (2.43), $\Omega''_{k+1}$ (2.45) | unchanged (LFR §I.3) |
| Approximate minimum | $\psi^{(k)}(\tilde\theta)=\psi(\mathbb B_k(W_k),(\mathbb B_k(W_k)\cap\Omega^c_{k+1})\cup\Lambda_{k+1};\tilde\theta)$ (2.17) | Lemma 2.2 with the generating sets of LFR §II.2.3; I-2 |
| Localized minimum | $\psi^{(k)}(\square',\theta):=\psi^{(k)}(\tilde\theta,s{=}0)$ on $\square'$, pair $(X_0,X_1)=(\square',R_{k+1}(\square'))$; $|\delta\psi^{(k)}(\square')|<e^{-R_k}$ (2.18)–(2.19) | LOC I-4b (v), variation V5 |
| Substitution | $\psi_k=\psi^{(k)}(\square',\theta)+\beta_k^{-1/2}C^{(k)1/2}(\square',0)\hat\psi$ on $\square'\subset\Omega_{k+1}$ (2.20), (2.35), (2.39) | covariance of Lemma 2.4 (no $\nu$-part, D-FL.1) at $s=0$ |
| Main action | (2.26), (2.33), (2.38): $\frac12aL^{-2}\|\theta-Q\psi_k\|^2+A^*_k(Z^c_k;\psi_k,\phi_k)=A^{\eta*}_{k+1}(Z^c_k,\mathbb B_{k+1};\theta,\phi_{k+1}(\tilde\theta))+\frac{\beta_k^{-1}}2\|\hat\psi\|^2+V^{(k)}_{\rm eff}$ | Lemma 2.3 restricted to $Z^c_k$; $V_{\rm eff}$ = $V^{(k)}(Z^c_k)$ of (2.4) + $V^{(k)}_\nu$ + the $\delta_0^{(k)}$ terms (2.37) + the form on $\Omega_1(W_k)\cap Z_k$ (2.31)–(2.32) + the surface term |
| Jacobian | $-\frac12N\log\beta_k|\Omega_{k+1}|+\log\det C^{(k)1/2}_{\rm loc}=\ldots-\frac12D^{(k)}-\delta D^{(k)}$ (2.40)–(2.41) | $D^{(k)}=\mathrm{Tr}\,\mathbb L$ on $\Omega_{k+1}$ (Lemma 2.4 (c)) |
| Characteristic functions | (2.42)–(2.47); P5 Lemma 2.1 | LFR Lemma IV.1.2 (proved there) |
| Separation formulas | (3.1)–(3.2) $\mathcal B''^{(k+1)}$; (3.8)–(3.9) $\mathcal R'^{(k+1)}$; (3.10)–(3.11) $\mathcal R'^{(k+1)}_{n-1}$; (3.12)–(3.17) $\mathscr E'^{(k+1)}_1,\mathscr F''^{(k+1)}_0$, measures $d\mu_{t,u}$ (3.16) | the interpolation identity of Prop 2.6 applied to each added interaction term |
| Result | (3.18) | input of §3 and §5 |

The fluctuation integral is over $\hat\psi$ on the unit sites of $\Omega''_{k+1}$ with the measure $\nu_{p_1}$ of (2.5) restricted there; on $\Omega_{k+1}\setminus\Omega''_{k+1}$
the variables $\hat\psi$ (P6: $\psi'_k$) are internal variables of the large-field operator (LFR §II.5.1). Every function appearing in an exponential of (3.18) depends
on $Z^c_k,\Omega_{k+1}$ and the history only, not on $\mathsf P,\mathsf Q,\mathsf R,\Omega''$ (P5 p. 513 [checked]); this is what makes the localization expansions of §3
uniform.

**Definition 2.7 (the auxiliary generating set of the step; P6 pp. 23–24, 29).** $\Omega^\sharp_{k+1}:=$ the union of the $\pi_{k+1}$-cubes meeting $(Z^c_k)^\approx$, and
$\mathbb B^\sharp_{k+1}:=(\mathbb B_k(W_k)\cap(\Omega^\sharp_{k+1})^c)\cup(\Omega^\sharp_{k+1})^{(k+1)}$. The decoupling cover of LOC §1.2 for every expansion of the step is built from
$\mathbb B^\sharp_{k+1}$; the operators, backgrounds and covariances are those of the actual generating sets ($\mathbb B_k(W_k)$, $\mathbb B_{k+1}$ and the local ones).

**Lemma 2.8 (the auxiliary cover is admissible; conditional on an OPEN assertion).** **[v2: FL-A02]** See notes/phase1/VMOD.md (in preparation). The calculation below establishes only the geometric separation, not the new-interface margins or modular decoupling. (a) $\Omega^\sharp_{k+1}\subset W_k$ at distance $\ge([R_{k-1}]+1)ML^k$ from $W_k^c$, so $\mathbb B^\sharp_{k+1}$ is a generating set
with separation $\ge\varrho$ and it is cube-aligned (Def-L1) because $(Z^c_k)^\approx$ is a union of $\pi_k$-cubes and $\pi_{k+1}$-cubes are unions of $\pi^1$-cubes. (b) On
$\Omega^\sharp_{k+1}\setminus\Omega_{k+1}$ the actual blocks (side $L^k$) are finer than the cover scale ($M_1L^{k+1}$); LOC §1.1b shows that (Cov3), (K), NC, DG1–DG7 then hold
with $C_\chi$ multiplied by $L$, so LOC I-4a–c and I-5 hold with the cover of $\mathbb B^\sharp_{k+1}$ and constants depending on $(d,L,N,\kappa_1)$ only. (c) Every
$X\in\mathcal D_j$, $X\subset(Z^c_k)^\approx$, has $X\subset X_1\subset\Omega^\sharp_{k+1}$ ($X_1$ of LOC §4.0), and the output domains lie in the last layer, so $\tilde d^{\rm cov}=d^{\rm cov}_{k+1}$
there (LOC V4). *Sketch.* (a) $(Z^c_k)^\approx$ is $[R_k]$ cubes thick around $Z^c_k$ and $W_k=(Z^c_k)^{\approx2}$ adds the same margin (LFR Lemma I.3.5 (f)); one
$\pi_{k+1}$-cube is $L$ cubes of $\pi_k$, much less than the margin. (b) LOC §1.1b, verbatim. (c) LOC §4.0. UNCERTAIN: LOC's open item 5 (separation at the new interface of
$\mathbb B^\sharp$, and $r_0,r_1$) is answered by (a) only for the separation; the margins $r_0=8$, $r_1=2$ are inherited because $X_1\subset\Omega^\sharp_{k+1}$ with an
$R_k$-margin.

### 2.8 Both conventions, and the switch at $k_0$

For $k<k_0$ every object of the step is $\nu$-free (backgrounds, covariance, the RG system (E1-free)–(E3-free) of SF §3.7, `matrixFree`); for $k>k_0$ every
object is complete (P4's system, `matrixInfty`). At $k=k_0$ the fluctuation integral is $\nu$-free (it is built from the scale-$k_0$ data) and the output must be
complete. We follow P6's own suggestion (p. 11 [checked]: "we could divide the operations in the case $k=k_0$ into two steps") and **switch before renormalizing**.

**Lemma 2.9 (the switch; scalar quadratic identity proved, RG conclusion conditional on an OPEN assertion).** **[v2: FL-A07]** See notes/phase1/RGFREE.md (in preparation) for the joint $\xi$ dependence and scale-sensitive RG estimates. The calculation below proves the scalar switching cost. Let $k=k_0$, let $\phi^0:=\phi^0_{k+1,u}(\theta)$ be the unrenormalized $\nu$-free
background of the step and $\phi^\nu:=\phi^\nu_{k+1,u}(\theta)$ the complete one (same data, mass $\mu=\nu_{k+1,u}$), and $\delta\phi:=\phi^0-\phi^\nu$. Then:
(a) $A^\star_{k+1,u}(\theta,\phi^0)=A^\eta_{k+1,u}(\theta,\phi^\nu)+\frac12\langle\delta\phi,(H^\nu+\alpha^\nu)\delta\phi\rangle$ exactly ($H^\nu=-\Delta+a_{k+1}Q^*Q+\mu$, $\alpha^\nu$ the multiplier of $\phi^\nu$), and
$\delta\phi$ is the solution of BG Prop 5.1 for the mass-free operator $H^0=H^\nu-\mu$ with $\phi_0=\phi^\nu$, $\alpha_0=\alpha^\nu$, $\delta\Psi=0$, $f_1=\mu(\phi^\nu-h)$, so $|\delta\phi|$-norms $\le K_2\nu_{k+1,u}|\phi^\nu-h|\le2K_2\nu_{k+1,u}$ (unit scale).
(b) The *switching term* $\mathscr S:=-\beta_{k+1,u}\frac12\langle\delta\phi,(H^\nu+\alpha^\nu)\delta\phi\rangle$, and the re-expression terms
$\mathscr E^{(j)}(\psi^{(j),0}_{k+1,u})-\mathscr E^{(j)}(\psi^{(j),\nu}_{k+1,u})$, $j\le k_0$ (composition (6.2) with $\phi^0$ resp. $\phi^\nu$), and the corresponding $\mathscr F$-differences,
have localization expansions over $Y\in\mathcal D_{k+1}$ with terms analytic on the domains of Theorem 3.1 and bounded by $C_{\rm sw}\beta_{k+1}^{-1}e^{-(2\kappa-1)d^{\rm cov}_{k+1}(Y)}$ (resp.
$C_{\rm sw}\beta^{-1}\alpha_0^{-1}E_0$ for the re-expression terms), $C_{\rm sw}=C(d,L,N,\kappa_1)L^{2d}$.
(c) The insertion of these terms before the complete-convention renormalization is an **OPEN** RG assertion: the terms depend jointly on $\xi$ through the renormalized background and re-expression maps, and their derivatives can change the matrix. The exact scale-sensitive input required by `rg_step_infty` is delegated to notes/phase1/RGFREE.md (in preparation). No assertion that the matrix is unchanged follows from (a)–(b).

*Proof.* (a) Lemma II.7.3 of LFR (the chord identity) for the minimiser $\phi^\nu$ of $A^\eta_{k+1,u}$ and the sphere configuration $\phi^0$; $\phi^0$ solves $H^0\phi^0+\alpha^0\phi^0=S$, so
$H^\nu\phi^0+\alpha^0\phi^0=S+\mu\phi^0$; subtracting $H^\nu\phi^\nu+\alpha^\nu\phi^\nu=S+\mu h$ and moving $\mu\delta\phi$ to the left gives $(H^0+\alpha^\nu+\delta\alpha)\delta\phi+\delta\alpha\,\phi^\nu=\mu(\phi^\nu-h)$,
$(\phi^\nu+\delta\phi)\cdot(\phi^\nu+\delta\phi)=1$, $\delta\alpha=\alpha^0-\alpha^\nu$; uniqueness in Prop 5.1 identifies the difference. (b) $\beta_{k+1,u}\nu_{k+1,u}=
\beta_kL^{d-2}\nu_kL^2\le e^{2\epsilon}L^d$ (LFR D-IV.11), so per unit block $\beta_{k+1,u}|\delta\phi|^2\le4K_2^2\beta_{k+1,u}\nu_{k+1,u}^2\le4K_2^2e^{4\epsilon}L^{2d}\beta_{k+1,u}^{-1}$. The localization is
LOC I-4a (mode U, data $f_1=\mu(\phi^\nu-h)$) and Lemma AE, with the prefactor just computed (the decay rate is limited only by $\kappa_1$, §3.3). The re-expression terms:
$\psi^{(j),0}-\psi^{(j),\nu}$ is (6.2) applied to $\delta\phi$ (affine), of scaled size $\le C s_{jk}\cdot2K_2\nu_{k+1}$; with Lemma 3.2 below and the Cauchy estimate on a disc of radius
$\asymp\varepsilon_{k+1}$ the first variation of $\sum_j\mathscr E^{(j)}$ is $\le CE_0\nu_{k+1}\varepsilon_{k+1}^{-1}\le CE_0\alpha_0^{-1}L^d\beta^{-1}\eta^{\frac{d-2}2+\gamma}$ per unit block. (c) remains conditional on the named OPEN RG assertion. The preceding $O(\beta^{-1})$ scalar cost does not bound $\partial_\xi$ of the re-expression terms, nor does it by itself verify the scale factor in the landed `rg_step_infty` hypothesis `hηbd`. $\square$

*Comparison.* SF §3.7 estimated the switch contribution to $\eta$ as $C\nu_{k_0}p(\beta)^2\varepsilon^{-2}$ and marked the size condition UNCERTAIN. The chord identity shows the
switching term is *quadratic* in $\delta\phi=O(\nu)$, hence $O(\beta^{-1})$ per block: the condition holds with room (Finding F-3). P6's one-step treatment (the term
$\nu_{k+1}(\phi_{k+1}-h)$ in $f_0$ of (2.24), which makes $c_2^{(k+1)}$ not second order in $\xi$) is avoided.

---
## 3. I-8: the localization and cluster expansions of the step

### 3.1 Statement

Standing hypotheses for §3: the step $k\to k+1$, $k\ge1$; a representation whose small-field data satisfy Def-6 resp. Def-7 (D2) at scale $k$ with
rate $\kappa$ (§1.4, domains $\Xi^c$ by F-1), boundary terms with (D7) (constant $B_0$, rate $\kappa$); the domains of the step (§2.7) and the auxiliary set
$\mathbb B^\sharp_{k+1}$ (Definition 2.7); $\Omega:=\Omega_{k+1}$, sizes $d^{\rm cov}_{k+1}$ and $d^{\rm cov}_{k+1}(\cdot\bmod\Omega^c)$ (Definition 1.1). The **whole-lattice case** is
$Z_k=\varnothing$: then $\Omega_{k+1}=\Omega''_{k+1}=\mathbb T$, $\mathcal B^{(k)}=\mathcal R^{(k)}=0$, $C^{(k)1/2}_{\rm loc}$ may be replaced by $C^{(k)1/2}$ (P4), and all
"mod $\Omega^c$" sizes are plain ones. Analyticity spaces: for new small-field terms $\Xi^c_{k+1}(\mathbb B_{k+1}(Y);1,\varepsilon_{k+1})$; for boundary terms the H7 domain of
LFR Definition II.3.5 (d) (P5 (1.36)–(1.37)); always $\|g\|_{\ell^1}<1$ complex. Rates:
$$\kappa_U:=2\kappa-1,\qquad\kappa_a:=2\kappa-\tfrac52-3\kappa_0-c_1,\qquad\kappa_b:=\kappa_a-\kappa_0-1 .$$

**Theorem 3.1 (I-8; P4 Props 2.1, 2.2, 4.1, 4.2; P5 Props 3.1–3.4; P6 Props 2.1–2.3 and §4).** Assume (IC) of §3.7 and $\beta$ large (after all
other constants). Then the following localization expansions exist; every term is analytic on the stated domain (jointly with all parameters
named), real for real arguments, $O(N)$-invariant (resp. equivariant for $\mathscr M$), covariant under the Euclidean symmetries preserving $\pi_{k+1}$, and depends
on the variables only through their restriction to its localization domain $Y$ (fluctuation variables $\psi'$ on $Y\cap(\Omega_{k+1}\setminus\Omega''_{k+1})$).
Domains $Y$ in (a)–(e) are of the form $\hat Y(S)\in\mathcal D_{k+1}(\bmod\,\Omega^c)$ of Definition 1.1.
- **(a)** $\mathscr E''^{(k+1)}_0(z)=-\frac12D^{(k)}(z)+\mathscr E'^{(k+1)}_1(z)$, $z\in T^{(k+1)}_L\cap\Omega_{k+1}$ (P5 (3.14), (3.17)): $=\sum_{Y\ni z}\mathscr E''^{(k+1)}_0(z,Y)$ with
  $|\mathscr E''^{(k+1)}_0(z,Y)|\le(NL^dB_{\mathbb L}+1)K_0\,e^{-\kappa_a d^{\rm cov}_{k+1}(Y\bmod\Omega^c)}$; if $Y\subset\Omega''_{k+1}$ the term equals the whole-torus term.
- **(a′)** $\mathscr E'^{(k+1)}_1(Z^c_k\cap\Omega^c_{k+1})=\sum\mathscr E''^{(k+1)}(Y)$ over $Y$ meeting $\Omega_{k+1}$ and $\Omega^c_{k+1}$, $|\cdot|\le e^{-\kappa_b d^{\rm cov}(Y\bmod\Omega^c)}$.
- **(b)** $\mathscr M''^{(k+1)}_0(x;g)=\sum_{Y\ni x}\mathscr M''^{(k+1)}_0(x,Y;g)$ with $\beta_k^{-1/2}|\mathscr M''^{(k+1)}_0(x,Y)|\le\frac12\beta^{-1/4}(L^{-1}\eta)^{\frac{d-2}2+\gamma-\alpha_1}e^{-\kappa_b d^{\rm cov}(Y\bmod\Omega^c)}$.
- **(c)** $\mathcal B''^{(k+1)}$ of P5 (3.2) $=\sum\mathcal B''^{(k+1)}(Y)$ over $Y$ meeting $\Omega^c_{k+1}$ and $\Omega_{k+1}$, $|\cdot|\le\beta_k^{-1}e^{-\kappa_a d^{\rm cov}(Y\bmod\Omega^c)}$.
- **(d)** $\mathcal R'^{(k+1)}_m:=\mathcal R'^{(k+1)}-\delta D^{(k)}$ (P5 (3.9), p. 520) $=\sum_Y\mathcal R'^{(k+1)}_m(Y)$, $|\cdot|\le\frac12\beta_{k+1}^{-m-1}e^{-\kappa_b d^{\rm cov}(Y\bmod\Omega^c)}$; for $Y\subset\Omega''_{k+1}$ the
  term does not depend on $Z^c_k,\Omega_{k+1},\Omega''_{k+1}$.
- **(e)** $\mathcal R'^{(k+1)}_{n-1}$ of P5 (3.11), $2\le n\le m$: the terms $\mathcal R^{(k)}_n(X)$ with $X\cap\Omega_{k+1}=\varnothing$ unchanged, plus $\sum_Y$ with $|\cdot|\le\frac12\beta_{k+1}^{-n}e^{-\kappa_b d^{\rm cov}(Y\bmod\Omega^c)}$.
- **(f)** **[v2.1: FL-A03] Conditional on the named OPEN inputs of the proof audit in §3.6; see notes/phase1/VMOD.md §2.** (P6 Props 2.1, 2.2, printed pp. 8–9.) The second term and the sum over $j$ of P6 (2.19), and the $\mathscr F$-analogue, are $\sum_{X\in\mathcal D_k,X\subset W^\sim_k\cap\Omega^c_{k+1}}(\cdot)(X)+\sum_{Y\in\mathcal D_{k+1}(\bmod\Omega^c),Y\cap Z_{k+1}\ne\varnothing}(\cdot)(Y)$
  with bounds $C_fE_0e^{-(\kappa-1)d^{\rm cov}_k(X)}$ and $C_fE_0e^{-(2\kappa-\kappa_0-1)d^{\rm cov}_{k+1}(Y\bmod\Omega^c)}$ ($E_0$ replaced by $2$ for $\mathscr F$).
- **(g)** (P4 Prop 4.1, P6 Prop 2.3.) For $\xi$ in the polydisc $\mathcal P_\epsilon=\{|\xi_i|<\epsilon\}$, $\epsilon\le\epsilon_R$: $C_1^{(k+1)}(z)$, $C_2^{(k+1)}(z)$, $\mathscr E^{(k+1)}_u(z)$ of §3.6 have
  expansions over $Y\ni z$ with terms analytic jointly on $\Xi^c_{k+1}(\mathbb B_{k+1}(Y);1,\varepsilon_{k+1})\times\mathcal P_\epsilon$ and bounds $C_4'\varepsilon_{k+1}^2\epsilon$, $C_4'\varepsilon_{k+1}^2\epsilon^2$,
  $(NL^dB_{\mathbb L}+1+C_5E_0\epsilon)K_0$ times $e^{-\kappa_a d^{\rm cov}_{k+1}(Y)}$; terms with $Y\subset(Z^c_{k+1})^\approx$ equal the whole-lattice terms.
- **(h)** (P4 Prop 4.2.) $\mathscr M^{(k+1)}(x)$ of (3.11) below has an expansion with the (H.7) bound in which $c_9$ is replaced by $\frac12\beta^{-1/4}+C_6\epsilon L^{(k+1)(2\gamma-\alpha_1)}$ and $\kappa$ by $\kappa_b$.

**Status [v2.1: FL-A03, FL-A13].** The algebraic decomposition and the landed termwise I-6 conclusions are proved under their displayed premises. Parts (a)–(e), (g), (h) are **conditional on OPEN assertions**: the actual RG-to-termwise premises, the auxiliary cover and NC, the fluctuation I-5, and for (c) the modular (Vmod). Part (f) is **conditional on OPEN assertions**: the actual old-term `PremisesTerm`/`SumConds` and H7 domain verification (OPEN-LOCAL-I6), mixed-cover H7 response (OPEN-OLD-H7-DECAY), Vmod with the extra coarse halo, and the finite modular resummations. §3.6 proves the algebra and the conditional prefactor, and identifies the missing hypotheses; see notes/phase1/VMOD.md §2. The PROVED abstract AE, GM and Mayer declarations yield the displayed bounds only after those premises are established. The constants
$C_4',C_5,C_6,C_f$ depend on rows 0–6b and on $\kappa$, not on $E_0,B_0,\beta$.

### 3.2 The termwise irrelevant decomposition (I-6 localized; P6 (4.13)–(4.14))

**[v2: FL-A01]** Write $\operatorname{st}_+(y)=\{y\}\cup\{y+e_\mu:1\le\mu\le d\}$. The forward differences in the counterterm use this star even when $y$ is on the boundary of $X$. For each $X\ni y$ choose $X^\star$ to be $X$ together with the at most $d$ additional $\pi'_j$-cubes needed to contain $\operatorname{st}_+(y)$; use the connected cube hull if a covering convention requires it. The choice is translation covariant and local. A tree for a chosen cover of $X$ meets a cover cube containing $y$. Extend it through that cube to each new cube. Each extension has length at most $4LM$ in scale-$j$ units, so
$$d^{\rm cov}_j(X^\star)\le d^{\rm cov}_j(X)+c_\star,\qquad c_\star:=4dL.\tag{3.0}$$
There are at most $n_\star:=2^{(2d+1)L^d}$ possible $X$ for a fixed $X^\star$ (only the at most $2d+1$ cubes meeting the star can be removed); this deliberately loose constant is independent of scale and volume. Consequently a term bounded by $Ee^{-(\kappa-1)d^{\rm cov}_j(X)}$ has, as an $X^\star$-term, the bound $Ee^{(\kappa-1)c_\star}e^{-(\kappa-1)d^{\rm cov}_j(X^\star)}$, and every entropy sum over the new supports costs at most $n_\star e^{\kappa_0c_\star}K_0$. The rate is unchanged; the cost is a fixed prefactor. In a subdomain application $y\in Z_k^c$ has the $W=(Z_k^c)^\approx$ margin, so $\operatorname{st}_+(y)\subset W$ and this enlargement remains in the auxiliary cover of Definition 2.7. The cover and its interface margins remain the OPEN assertion of Lemma 2.8; see notes/phase1/VMOD.md (in preparation).

Use the notation of SF §2.2–§2.3: $s=s_{jk}$, $\sigma=C_0s$, $R=\varepsilon_k/\varepsilon_j$, $P_0=(e_1,\nu_je_1)$, and $f_X,a_X,B_X,m_X$ for the tensors of the single term $\mathscr E(y,X)$. Set
$$T_X=f_X(P_0)+\partial_uf_X(P_0)(u-1)+\partial_vf_X(P_0)(v-\nu_j),\qquad A_{y,X}=\tfrac12\sum_{x\in X}a_X(x-y)(\psi(x)\cdot\psi(x)-\psi(y)\cdot\psi(y)),$$
$$\Phi_{y,X}=-\tfrac14\sum_{\mu,\nu}S_X^{\mu\nu}\left[\partial_\mu\psi\cdot\partial_\nu\psi-(\hat\psi\cdot\partial_\mu\psi)(\hat\psi\cdot\partial_\nu\psi)\right](y),\quad S_X^{\mu\nu}=\sum_{x,x'}B_X(x,x')(x-x')_\mu(x-x')_\nu,\quad \hat\psi=\psi(y)/\sqrt{\psi(y)\cdot\psi(y)},$$
and $I(y,X)=\mathscr E(y,X)-T_X-A_{y,X}-\Phi_{y,X}$.

**Lemma 3.2 (termwise irrelevance; proved conditional on the PROVED landed termwise I-6 declarations and their stated premises).** Assume the termwise bounds and analyticity premises `PremisesTerm` and the summed cancellation premises `SumConds` of `Balaban/SmallField/RenormTermwiseDefs.lean`. Then (i) $\sum_XT_X=\sum_X\Phi_{y,X}=0$, $\sum_XA_{y,X}=A_y$, and $\sum_{y\in\Lambda}A_y=0$ on a torus. (ii) $I(y,X)$ depends on $\psi$ only on $X\cup\operatorname{st}_+(y)$, hence on $X^\star$; $T_X$ uses $y$, $A_{y,X}$ uses $X$, and $\Phi_{y,X}$ uses the star. The terms are $O(N)$-invariant and analytic on the intersection of the term's tube with $\{\psi(y)\cdot\psi(y)\in\mathbb C\setminus(-\infty,0]\}$, including an open neighbourhood of every point of that intersection. (iii) Under (Σ1), (Σ2), for all $j\le k$,
$$|I(y,X)|\le C_IE_0s^{d+\alpha_3}e^{-(\kappa-1)d^{\rm cov}_j(X)}\le C_Ie^{(\kappa-1)c_\star}E_0s^{d+\alpha_3}e^{-(\kappa-1)d^{\rm cov}_j(X^\star)},\quad\alpha_3=1-2\gamma-\alpha_1>0.\tag{3.1}$$
(iv) For $W=(Z_k^c)^\approx$ and $y\in Z_k^c$, let $A^W_y$ be the restriction of $A_y$ to $x\in W$ and let $A^W_{y,X}$ be the corresponding restriction of $A_{y,X}$. Then
$$\sum_{X\ni y,\,X\subset W}\mathscr E(y,X)-A^W_y=\sum_{X\ni y}I^W(y,X),\quad I^W(y,X):=\begin{cases}I(y,X),&X\subset W,\\-T_X-\Phi_{y,X}-A^W_{y,X},&X\not\subset W.\end{cases}\tag{3.2}$$
The support of $I^W(y,X)$ is $(X\cap W)\cup\operatorname{st}_+(y)$ (the field $b$ is included as before). For $X\not\subset W$ its bound is $C_mE_0s^me^{-R_k/2}e^{-(\kappa-1)d^{\rm cov}_j(X)}$ for each fixed $m$, with the same fixed enlargement cost if indexed by $X^\star$. The comparison with P5 (1.8) uses $a^{(j)}=v^{(j)}_1+\nu_jv^{(j)}_2$ at the reference point and the irrelevant remainder estimates of SF Step 5; that comparison remains conditional on the cited P5/P6 transfer.

*Proof.* `Ttw_tsum_zero`, `Phitw_tsum_zero`, `Ax_tsum_eq` and `Aterm_torus_sum_tw` prove (i), with exactly the separate summed hypotheses in `SumConds`. `Itw_congr` proves the support $X\cup\operatorname{st}_+(y)$; `IW_congr` proves the restricted support in (iv). `Ttw_analytic`, `Ax_analytic`, `Phitw_analytic` and `Itw_analytic` prove (ii): the square root is analytic on the slit plane, whereas $\Phi$ needs only its nonzero denominator. `termwise_irrelevant_all_scales` proves the first bound in (3.1) from `PremisesTerm`; (3.0) gives the second. `energyW_sub_AW_eq_tsum_IW` proves the equality (3.2), and `IW_bound_outside` proves its far-support estimate. To see the geometric factor in that last estimate, $X\ni y\in Z_k^c$ and $X\not\subset W$ force a connected path from $y$ across the $[R_k]$-cube collar, whence $d_j^{\rm cov}(X)\ge L^{k-j}[R_k]-O(1)$ by (G5); split its exponential in half and absorb any fixed power of $s^{-1}$ in the other half. All cited declarations concern the abstract term family. Identifying the actual RG terms with `PremisesTerm` and `SumConds`, including the tube bounds on the scaled evaluation locus, is the stated hypothesis here; the landed declarations do not prove that identification. $\square$

**I-5 input.** The evaluation of $I(y,X)$ is on the scaled locus (Σ1), (Σ2) of SF, which lies in its tube and in the slit-plane component around the real unit spin. Apply I-5 to the local support $X^\star$, with size $d^{\rm cov}_j(X^\star)$, source neighbourhood containing that locus, and prefactor $C_Ie^{(\kappa-1)c_\star}E_0s^{d+\alpha_3}$. Its conclusion contains the thickening of $X^\star$, so the forward differences are genuinely inside the decoupling core. The fixed factor $n_\star e^{\kappa_0c_\star}$ is included in $C_U$ of (3.4). For a boundary term the modular I-5 is still OPEN; see notes/phase1/VMOD.md (in preparation).

### 3.3 Two variants of I-5, and the localized interaction

**Variant (V0) (scaled hypothesis; conditional on the OPEN fluctuation-variable I-5 extension).** In LOC Theorem I-5 the hypothesis on $\mathscr E(X;\cdot)$ may be weakened to:
analytic on an open neighbourhood of $\mathcal S_j(X):=\{\psi(\mathbb B_j(X),\mathbb B_k(X);\hat\Psi)|_X:\hat\Psi\in\Xi^c_k(\mathbb B_k(X);1,\varepsilon_k)\}$ and bounded there by $Ee^{-(\kappa-1)d_j(X)}$. Indeed
Lemma DL step (5) evaluates $\mathscr E$ only at points of $\mathcal S_j(X)$, and Lemma AE uses only the bound at these points. By (R-S) (SF §1.7) and (Ξ4) (LOC §4.0),
every point of $\mathcal S_j(X)$ satisfies (Σ1) with $\sigma=C_0s_{jk}$ and (Σ2) on $X$, so Lemma 3.2 (iii) applies on $\mathcal S_j(X)$. (This is P6's "Lemma 4.2[3] holds ... with a
slight modification", p. 29; ER-095.)

**Variant (Vmod) (boundary terms; conditional on an OPEN assertion).** **[v2: FL-A02]** See notes/phase1/VMOD.md (in preparation). The required input is a modular I-5 expansion for every old boundary term $\mathcal B(X)$ with $X\in\mathcal D_k(\bmod\Omega_k^c)$ and $X\cap\Omega_{k+1}\ne\varnothing$, analytic on the H7 neighbourhood, with input bound $B'e^{-(\kappa-1)d_k^{\rm cov}(X\bmod\Omega_k^c)}$ and output supports $Y\in\mathcal D_{k+1}(\bmod\Omega_{k+1}^c)$ satisfying
$$|\mathcal B(X,Y)|\le B'e^{-\kappa_0d_k^{\rm cov}(X\bmod\Omega_k^c)-2\kappa d_{k+1}^{\rm cov}(Y\bmod\Omega_{k+1}^c)}.$$
The component, margin, source-domain and output-domain conditions are part of that OPEN input. The landed background-only `i5_background` does not imply this variant.

**The interaction.** For the measures of P5 (3.16) (and their variants (3.2), (3.9), (3.11)) define, with $\psi'(\hat\psi):=\beta_k^{-1/2}C^{(k)1/2}_{\rm loc}\hat\psi$ and a complex parameter $\sigma$
introduced linearly as in P6 (4.1) (so that $\sigma=1$ gives the true exponent and $\sigma=0$ gives $0$):
$$\mathscr U_{t,u}(\sigma;\hat\psi):=-\beta_k^{-1/2}\sigma\!\int_0^1\!\!dt'\tfrac{(1-t')^2}2\,V^{(k)\prime\prime\prime}\big(\sigma t'\psi'(t\hat\psi)\big)\big[C^{1/2}t\hat\psi\big]^{3}-\beta_k^{-1/2}\sigma(\beta_k\nu_k)\!\int_0^1\!\!dt'\,V^{(k)\prime}_{\nu,1}\big(\sigma t'\psi'(t\hat\psi)\big)\big[C^{1/2}t\hat\psi\big]$$
$$+\beta_k^{-1/2}\sigma\!\int_0^1\!\!dt'\,\big\langle\delta\mathscr E_k'\big(\sigma t'\psi'(t\hat\psi)\big),C^{1/2}t\hat\psi\big\rangle+\beta_k^{-1/2}\sigma\!\int_0^1\!\!dt'\,\big\langle\delta\mathscr F_k'\big(\sigma t'\psi'(u\hat\psi),g\big),C^{1/2}u\hat\psi\big\rangle,\tag{3.3}$$
where $V^{(k)}_{\nu,1}:=\nu_k^{-1}V^{(k)}_\nu$ (only for $k\le k_0$; $\beta_k\nu_k\le e^{2\epsilon}$), $V^{(k)}$, $\delta\mathscr E_k$, $\delta\mathscr F_k$ restricted to $Z^c_k$ as in P5 (2.29)–(2.30), (2.49), and
$C^{1/2}=C^{(k)1/2}_{\rm loc}$. Put $R_\sigma:=\beta^{1/8}\eta^{-(\gamma-\alpha_1/2)}$.

**Proposition 3.3 (localized interaction; P6 Lemma 4.1, Lemma 4.2, (4.32)–(4.34); conditional on the OPEN (Vmod), auxiliary-cover and fluctuation I-5 assertions).** **[v2: FL-A01, FL-A02]** For $(\theta,h)$ in the analyticity space of (4.25) (P6),
real $\hat\psi$ with $|\hat\psi(x)|<p_1(\beta_k)$, $\|g\|_{\ell^1}<1$, $|\sigma|<R_\sigma$, $t,u\in[0,1]$:
$$\mathscr U_{t,u}(\sigma;\hat\psi)=\sum_{Y\in\mathcal D_{k+1}(\Omega^\sharp_{k+1}):\,Y\cap\Omega_{k+1}\ne\varnothing}\mathscr U_{t,u}(Y;\sigma,\hat\psi),\qquad|\mathscr U_{t,u}(Y)|\le\varepsilon_Ue^{-\kappa_Ud^{\rm cov}_{k+1}(Y)},\qquad\varepsilon_U:=C_U(E_0+1)\alpha_0^{-1}\beta^{-\frac38+\frac{3\alpha_1}4},\tag{3.4}$$
each term depending on $(\theta,h,g,\hat\psi)$ restricted to $Y$, analytic in $(\theta,h,g,\sigma)$, vanishing at $\sigma=0$, with the symmetry properties of Theorem 3.1; terms with $Y\subset\Omega''_{k+1}$
do not depend on $Z^c_k,\Omega_{k+1},\Omega''_{k+1}$ and equal the whole-torus terms. The added potentials of the other measures have expansions of the same form, with labels in
$\mathcal D_{k+1}(\bmod\Omega^c)$ for the boundary part, and bounds: $\mathcal B''^{(k)}$-part (P5 (3.2)): $\beta_k^{-3/2}e^{-\kappa_Ud^{\rm cov}(Y\bmod\Omega^c)}$; $\mathcal R^{(k)}_p$-parts (P5 (3.10)):
$\beta_k^{-p-1/2}e^{-\kappa_Ud^{\rm cov}(Y)}$; $\delta V_{\rm eff},\delta\mathscr E',\delta\mathscr F',\delta\mathcal R'$ (P5 (3.9)): $\beta_k^{-m-2}e^{-\kappa_Ud^{\rm cov}(Y)}$.

*Proof.* All decoupling constructions use the cover of $\mathbb B^\sharp_{k+1}$ (Lemma 2.8) and one decoupling vector $s$ (LOC §1.1b). Constants $K_3$, $B_5$, $c_7$, $C_3$ are LOC's.
*The $V$-part.* For a block $z$ let $V^{(k)}(z;\psi',s)$ be (2.4) restricted to $B_{k+1}(z)$ with $(\phi',\alpha')=$ the solution of LOC I-4a **in mode P** with $\phi_0=\phi_{k+1}(s)$,
$\alpha_0=\alpha_{k+1}(s)$ (I-4b), data $\delta\Psi=\psi'$; $\phi^{(1)}(s)$, $\alpha^{(1)}(s)$ its linear parts and $\phi_2(s)$ the remainder; at $s=1$ mode P coincides with mode U
($\phi_{k+1}\cdot\phi_{k+1}=1$), so $V^{(k)}(z;\psi',1)=V^{(k)}(z;\psi')$. By I-4a (c) and the Cauchy argument of P6 (4.4)–(4.6), $|V'''(z;\cdot,s)[\delta\psi]^3|\le6\cdot36L^dK_3^2(C_3c_7)^{-1}|\delta\psi|^3$ for
$|\psi'|\le\frac1{18}C_3c_7$, uniformly on the polydisc $|s_P|\le e^{\kappa_1}$. Hence the $V$-part of (3.3) pre-localized in $z$, call it $F_z(s)$, is analytic on the polydisc and
$|F_z(s)|\le\beta_k^{-1/2}|\sigma|\,C_VL^dB_5^3p_1(\beta_k)^3$ ((AE1)); its locality in $s$ and in the data is I-4a (e), I-4b (iv), I-4c (v) ((AE2)). Lemma AE (landed
`abstract_expansion`) with $X_1$ the $r_0$-neighbourhood of $B_{k+1}(z)$ gives terms $F_{z,\mathcal C}$, $|F_{z,\mathcal C}|\le|F_z|e^{-(\kappa_1-1)|\mathcal C|}$; (GM3)–(GM4) with
$d_j(X)=0$ and $\kappa_1\ge4d(2L+1)^d\kappa$ resum them to $Y=Y[\mathcal C]$ with the factor $e^{-2\kappa d^{\rm cov}_{k+1}(Y)}$ (LOC V4: single-scale in $\Omega^\sharp_{k+1}$). Summing over the
blocks $z\subset Y$ costs $|Y|\le((2L+3)M)^d(1+d^{\rm cov})$ (Lemma 1.2 (G1)), i.e. $e^{-(2\kappa-1)d}$ and a constant. With (1.1),
$\beta_k^{-1/2}|\sigma|p_1^3\le C\beta^{-1/2+3\alpha'}\eta^{\frac{d-2}2-3\alpha'}R_\sigma\le C\beta^{-\frac38+\frac{3\alpha_1}4}\eta^{\alpha-\frac{\alpha_1}4}$ ($\alpha'=\alpha_1/4$), and $\alpha-\frac{\alpha_1}4>0$, $-\frac38+\frac{3\alpha_1}4<-\frac3{16}$ since $\alpha_1<\frac14$.
*The $\nu$-part* ($k\le k_0$) is the same with $V_{\nu,1}$ (linear and quadratic in $\phi'$, $|\phi^0_{k+1}-h|\le2$); bound $\beta_k^{-1/2}|\sigma|e^{2\epsilon}C K_3B_5p_1$.
*The $\delta\mathscr E$-part* (P6 (4.13)–(4.21)). **[v2: FL-A01]** By Lemma 3.2 (iv) (whole lattice: (i)), $\mathscr E_k(Z^c_k;\psi)=\sum_j\sum_{y\in Z^c_k}\sum_{X\ni y}I^W(y,X;\psi^{(j)}_k(\psi))$ exactly, the
cancelling terms $T_X,\Phi_{y,X}$ and the counterterm having been absorbed. Write $\delta\mathscr E'$ in (3.3) by the Cauchy formula in an auxiliary variable $\tau$ on $|\tau|=r$
(P6 (4.15)): the argument is $\psi'=(\beta_k^{-1/2}\sigma t'+\tau)tC^{1/2}\hat\psi$, of size $\le(\beta_k^{-1/2}|\sigma|+r)B_5p_1=:\delta_1$, and the radius $r:=\frac14\eta_\varepsilon\varepsilon_k\big((K_2+1)(2K_3+1)B_5p_1\big)^{-1}$
makes $\delta_1$ satisfy LOC (4.38) for $\beta$ large ($\beta_k^{-1/2}R_\sigma B_5p_1\ll\varepsilon_k$, as $\beta_k^{-1/2}R_\sigma\varepsilon_k^{-1}\le2\alpha_0^{-1}\beta^{-3/8}\eta^{\alpha_1/2}$). Apply I-5 in the scaled variant (V0) and its OPEN fluctuation-variable variant to the genuine local support $X^\star$ of each $I^W(y,X;\cdot)$, with $E=C_Ie^{(\kappa-1)c_\star}E_0s^{d+\alpha_3}$ and an open tube/slit-plane neighbourhood of the evaluation locus. Terms over $Y\supset X_1^\star$ are bounded by
$\beta_k^{-1/2}|\sigma|r^{-1}C_Ie^{(\kappa-1)c_\star}E_0s^{d+\alpha_3}e^{-\kappa_0d^{\rm cov}_j(X^\star)-2\kappa d^{\rm cov}_{k+1}(Y)}$. Resum with $Y$ fixed: the preimage count and entropy sum cost at most $n_\star e^{\kappa_0c_\star}K_0$ by (3.0), while $\sum_{y\in Y\cap T^{(j)}}s^{d+\alpha_3}\le L^d|Y|_{k+1}s^{\alpha_3}$ ($Y$ contains
$L^ds^{-d}|Y|_{k+1}$ unit sites of scale $j$), $\sum_{X\ni y}e^{-\kappa_0d}\le K_0$, $\sum_{j\le k}s^{\alpha_3}\le(1-L^{-\alpha_3})^{-1}$, $|Y|_{k+1}\le C(1+d^{\rm cov})$. With
$\beta_k^{-1/2}r^{-1}\le C\alpha_0^{-1}\beta^{-1/2}\eta^\gamma p_1\le C\alpha_0^{-1}\beta^{-1/2+\alpha'}\eta^{\gamma-\alpha'}$ (1.1) and $|\sigma|<R_\sigma$: the bound is
$CE_0\alpha_0^{-1}\beta^{-\frac38+\alpha'}\eta^{\frac{\alpha_1}2-\alpha'}e^{-(2\kappa-1)d^{\rm cov}_{k+1}(Y)}$, and $\frac{\alpha_1}2-\alpha'>0$. The terms $X\not\subset W$ carry $e^{-R_k/2}$ (Lemma 3.2 (iv)).
*The $\delta\mathscr F$-part* (P6 (4.22)–(4.23)): $\langle g,\phi_k\rangle$ gives $\langle g,\delta\phi_k(\psi')\rangle$, localized by I-4a and AE with prefactor $\sum_x|g(x)|K_3B_5\beta_k^{-1/2}|\sigma|p_1$; the
$\mathscr M^{(j)}$ terms as the $\delta\mathscr E$-part with $c_9\xi_j^{\frac{d-2}2+\gamma-\alpha_1}$ in place of $C_IE_0s^{d+\alpha_3}$ and without volume factor ($\|g\|_{\ell^1}<1$; P6 (4.23)): bound
$C(1+K_0c_9)\beta^{-\frac38+\alpha'}\eta^{\frac{\alpha_1}2-\alpha'}e^{-2\kappa d}$.
*Locality and the whole-torus property.* Each term is a function of the decoupled objects restricted to $Y$ (AE, (DG5′)); a term with $Y\subset\Omega''_{k+1}$ only involves
$I^W(y,X)$ with $X\subset Y\subset W$, which are the whole-lattice terms, and generating sets and data that coincide with the whole-torus ones on $Y$. *Vanishing at $\sigma=0$*: each
part of (3.3) carries the factor $\sigma$, and AE terms of an identically vanishing function vanish. *The other measures:* $\mathcal R^{(k)}_p$ as the $\delta\mathscr E$-part with
$\beta_k^{-p-1}$ in place of $C_IE_0s^{d+\alpha_3}$ and $\delta_1=\beta_k^{-1/2}B_5p_1$ (P6 p. 32); the terms of (3.9) are scalar products with $\delta_0^{(k)}(\beta_k^{-1/2}\hat\psi)$, which is
$\le\beta_k^{-m-4}$ (P5 (2.19), (2.34); P6 (4.31)), localized as above with radii $r_1=\beta_k^{m+2}$, $r=\beta_k^{m+3}$ (P6 (4.29)–(4.31)); the $\mathcal B''^{(k)}$-part (P6 (4.32)–(4.34)): an old
boundary term with $X\cap Z_k\ne\varnothing\ne X\cap\Omega_{k+1}$ has $d^{\rm cov}_k(X\bmod\Omega^c_k)\ge R_k$, so $|\mathcal B^{(k)}(X)|\le B_0e^{-\kappa R_k/2}e^{-\frac\kappa2d_k}\le\beta_k^{-2}e^{-(\kappa-1)d_k(X\bmod)}$
for $\beta$ large; (Vmod) and the resummation $\sum_{X\subset Y}$ ($K_0(3L^2)^d(1+d)$) give $\beta_k^{-3/2}e^{-(2\kappa-1)d^{\rm cov}(Y\bmod\Omega^c)}$. Collect the constants into $C_U$ (it
depends on rows 0–6b and on $\kappa$, $c_9\le1$). $\square$

### 3.4 The marked cluster expansion

The abstract input is MY + PE-L + PE-M (PE §§2.3–2.5; landed `mayer_marked`, `norm_D1_Ff_le`). We instantiate it with the block set
$\mathfrak B:=\{\pi_{k+1}\text{-cubes of }\Omega_{k+1}\}$ and the size $d_\Omega$ of Definition 1.1 on subsets of $\mathfrak B$; the hole is thereby removed from the polymer system:
two terms are incompatible iff their supports in $\Omega_{k+1}$ overlap, which is P6's connectivity modulo $\Omega^c$ (p. 44: "$Y_1\cap Y_2\cap\Omega_{k+1}\ne\varnothing$").

**Theorem 3.4 (marked cluster expansion; [v2: FL-A06, FL-A12]; proved conditional on the PROVED `mayer_marked` theorem and the geometric hypotheses of Lemma 1.2).** Let $\nu=\bigotimes_{b\in\mathfrak B}\nu_b$, $\nu_b$ the product of the measures
$\nu_1$ of (2.5) over the unit sites of $b\cap\Omega''_{k+1}$ (the Dirac measure on a point if there are none). Let $\mathcal T$ be a finite set of labels $Y$ (connected sets of
$\pi_{k+1}$-cubes with $Y\cap\Omega_{k+1}\ne\varnothing$) with sizes $\mathsf d(Y)$ equal to $d^{\rm cov}_{k+1}(Y)$ or $d^{\rm cov}_{k+1}(Y\bmod\Omega^c)$, satisfying
$\sum_{Y\in\mathcal T,\,b\subset Y}e^{-\kappa_0\mathsf d(Y)}\le K_0$. Let $H(Y;\Phi,u)$, $Y\in\mathcal T$, depend on the integration variable $\Phi$ only through $\Phi|_{Y\cap\Omega_{k+1}}$, be
measurable in $\Phi$, holomorphic in $u\in\mathcal U$ (open), and satisfy $|H(Y)|\le\varepsilon_He^{-\kappa_H\mathsf d(Y)}$ on $\mathrm{supp}\,\nu$; let $G=G(Y_0;\Phi,u)$ be one more such function with
$|G|\le F_0e^{-\kappa_G\mathsf d(Y_0)}$, $\kappa_G\ge\kappa_H$. Let $\kappa'\ge0$ with
$$\kappa_H\ge\kappa'+3\kappa_0+c_1+\tfrac32,\qquad 0<\varepsilon_H\le\varepsilon_{\rm PE}:=\big(8K_0^3c_1e^{(\kappa_H-2\kappa_0)c_G+c_1+\kappa'c_G}\big)^{-1}.\tag{3.5}$$
Then $\Xi:=\int e^{\sum_YH(Y)}d\nu\ne0$, and the expectation $\langle G\rangle:=\Xi^{-1}\int Ge^{\sum H}d\nu$ equals $\sum_{S}G^*(Y_0,S)$, the sum over sets $S\subset\mathfrak B$ with
$S\supset Y_0\cap\Omega_{k+1}$, where $G^*(Y_0,S)$ is holomorphic in $u$, depends on the non-integrated variables only through their restriction to $\hat Y(S)$, depends only on the $H(Y)$ with
$Y\cap\Omega_{k+1}\subset S$, on $G$ and on $\nu$ restricted to $S$, and
$$|G^*(Y_0,S)|\le C_{\rm PE}\,F_0\,e^{-\kappa_0\mathsf d(Y_0)}\,e^{-\kappa'd_\Omega(S)},\qquad C_{\rm PE}:=8K_0^2c_1e^{(\kappa_H-2\kappa_0)c_G+c_1+\kappa'c_G}.\tag{3.6}$$
Moreover $\log(\Xi/\Xi_0)=\sum_SP(S)$ ($\Xi_0$: $H\equiv0$) with $|P(S)|\le\varepsilon_HK_0C_{\rm PE}e^{-\kappa'd_\Omega(S)}$. **For two marks assume the strictly stronger $\varepsilon_H\le\varepsilon_{\rm PE}/4$.** Then the truncated expectation is $\sum_{S\supset(Y_1\cup Y_2)\cap\Omega_{k+1}}G^{**}(S)$ with
$$|G^{**}(S)|\le16\varepsilon_{\rm PE}^{-2}F_1F_2e^{-\kappa_0(\mathsf d(Y_1)+\mathsf d(Y_2))}e^{-\kappa'd_\Omega(S)}.\tag{3.6a}$$
This is the two-mark input for OBS X2; its application must verify the stronger activity bound.

*Proof.* If $F_0=0$, then $G=0$ almost surely and the one-mark claim is immediate; otherwise $F_0>0$. *Pre-summation.* For $S\subset\mathfrak B$ put $\tilde H(S):=\sum_{Y\in\mathcal T:\,Y\cap\Omega_{k+1}=S}H(Y)$. By (G4), $\mathsf d(Y)\ge d_\Omega(S)$ for such $Y$, so
$|\tilde H(S)|\le\varepsilon_He^{-(\kappa_H-\kappa_0)d_\Omega(S)}\sum_{Y\ni b}e^{-\kappa_0\mathsf d(Y)}\le\varepsilon_HK_0e^{-(\kappa_H-\kappa_0)d_\Omega(S)}$ ($b\in S$ fixed), and $\tilde H(S)$ depends on $\Phi$ only on $S$ and on the
other variables only on $\hat Y(S)$ (G4). Add the mark to the term of $S_0:=Y_0\cap\Omega_{k+1}$: $\tilde H_\lambda(S_0):=\tilde H(S_0)+\lambda G$, with
$$r:=\frac{\varepsilon_HK_0}{F_0}e^{\kappa_0\mathsf d(Y_0)}\ \Longrightarrow\ |\lambda G|\le\varepsilon_HK_0e^{\kappa_0\mathsf d(Y_0)-\kappa_G\mathsf d(Y_0)}\le\varepsilon_HK_0e^{-(\kappa_H-\kappa_0)d_\Omega(S_0)}\quad(|\lambda|<r),$$
using $\kappa_G\ge\kappa_H$ and $\mathsf d(Y_0)\ge d_\Omega(S_0)$. *MY + PE-L + PE-M.* Apply `mayer_marked` with terms $t=S$ (support $S$), $H_0:=2\varepsilon_HK_0\le\log2$, $\kappa_0$ for (G2T)
(Lemma 1.2 (G2) for $d_\Omega$), $\kappa_1:=\kappa_H-2\kappa_0$, $c:=c_G$ ((G3T) = Lemma 1.2 (G3)), $c_1$ ((G1)), polymers $=$ nonempty subsets of $\mathfrak B$ with size $d_\Omega$, $\kappa_{0P}:=\kappa_0$,
$K_{0P}:=K_0$, $c_P:=c_G$, and $\kappa'$. Its hypotheses: `hq` $2H_0K_0e^{\kappa_1c}c_1=4\varepsilon_HK_0^2e^{\kappa_1c_G}c_1\le\frac12$, `hκ` $\kappa'+\kappa_0+c_1\le\kappa_1-\frac32$, and `hα`
$2(2H_0K_0e^{\kappa_1c})c_1K_0e^{c_1+\kappa'c}=8\varepsilon_HK_0^3c_1e^{\kappa_1c_G+c_1+\kappa'c_G}\le1$; all follow from (3.5). Its conclusion gives $\langle G\rangle=\partial_\lambda\log\Xi_\lambda|_0=\sum_S\partial_\lambda P(S)|_0$
and $\sup_{|\lambda|<r}|P(S)|\le\alpha e^{-\kappa'd_\Omega(S)}$ with $\alpha=8\varepsilon_HK_0^3c_1e^{\kappa_1c_G+c_1+\kappa'c_G}$ (`pe_PY_bound` inside `mayer_pe`). Cauchy (`norm_D1_Ff_le`):
$|\partial_\lambda P(S)|\le r^{-1}\alpha e^{-\kappa'd_\Omega(S)}=C_{\rm PE}F_0e^{-\kappa_0\mathsf d(Y_0)}e^{-\kappa'd_\Omega(S)}$. $\partial_\lambda P(S)=0$ unless $S\supset S_0$ (PE-M (M1)). Locality: PE (c) and MY's
factorization (the activity of a polymer $S$ is an integral over the variables of $S$ of functions of the $\tilde H(S')$, $S'\subset S$). Holomorphy: PE (d), MY (ii). $\Xi\ne0$: PE (e).
$\log\Xi$: the same with $\lambda=0$. **[v2: FL-A06]** If $F_i=0$, then the corresponding mark vanishes almost surely and the two-mark bound is trivial; assume $F_1,F_2>0$ below. Take $r_i=\varepsilon_{\rm PE}(8F_i)^{-1}e^{\kappa_0\mathsf d(Y_i)}$. After pre-summation, each $|\lambda_iG_i|$ contributes at most $\varepsilon_{\rm PE}/8$ to the coefficient of $e^{-(\kappa_H-\kappa_0)d_\Omega(S)}$; hence the exact `mayer_marked` activity parameter is $H_0=\varepsilon_HK_0+\varepsilon_{\rm PE}/4\le\varepsilon_{\rm PE}K_0/2$ ($K_0\ge1$). Put $\kappa_1=\kappa_H-2\kappa_0$, $c=c_P=c_G$ and $K_{0P}=K_0$. Its `hq` left side is at most $\varepsilon_{\rm PE}K_0^2e^{\kappa_1c_G}c_1=1/(8K_0e^{c_1+\kappa'c_G})\le1/8<1/2$; `hκ` is exactly the first inequality of (3.5); `hα` is at most $4(\varepsilon_{\rm PE}K_0/2)K_0^2c_1e^{\kappa_1c_G+c_1+\kappa'c_G}=1/4$; and $H_0\le1/16<\log2$. The theorem's two-mark identity therefore applies. The two-variable Cauchy estimate gives at most $(1/4)(r_1r_2)^{-1}=16\varepsilon_{\rm PE}^{-2}F_1F_2e^{-\kappa_0(\mathsf d(Y_1)+\mathsf d(Y_2))}$, proving (3.6a). $\square$

*Losses.* From the label rate $\kappa_H$ to the output rate $\kappa'$: $\kappa_0$ (pre-summation of labels with the same support), $\kappa_0$ (MY entropy), $\frac32$ (MY), $\kappa_0+c_1$
(PE-L). The reserve $e^{-\kappa_0\mathsf d(Y_0)}$ comes from the mark's own decay and pays the later sum over $Y_0$. P6's corresponding losses are $5\kappa_0$ in (4.43), $\kappa_0$ in the tree
bound, $1$ and $1$ in (4.44), (4.51) (total $2+6\kappa_0$ for (4.54)). If PE-L is sharpened from $\alpha\le1$ to $\alpha c_1\le1$ (PE §3.6: $a(Y)=\alpha|Y\setminus S_0|\le\alpha c_1(1+d)$), the loss $c_1$
becomes $1$ (optional Lean refinement, §6.4).

### 3.5 Proof of Theorem 3.1 (a)–(e): the contributions of the fluctuation integral

Throughout, the measure of each item is the one of P5 named there, its interaction is expanded by Proposition 3.3 (labels in $\mathcal D_{k+1}(\Omega^\sharp_{k+1})$ and,
for the boundary part, in $\mathcal D_{k+1}(\bmod\Omega^c)$; $\varepsilon_H=\varepsilon_U$, $\kappa_H=\kappa_U$; the entropy hypothesis of Theorem 3.4 is Lemma 1.2 (G2)), and
Theorem 3.4 is applied with $\kappa'=\kappa_a$, which is admissible because $\kappa_U-\kappa_a=3\kappa_0+c_1+\frac32$ (equality in (3.5)) and, **[v2: FL-A06]** $\beta_*(\alpha_0,E_0)$ is increased until $\varepsilon_U\le\varepsilon_{\rm PE}/4$ so the same hypothesis also supports two marks. Integrals over the interpolation parameters $s,t,u\in[0,1]$ preserve the bounds and the analyticity. Final labels are the $\hat Y(S)$; a quantity indexed by labels
$Y$ with $Y\cap\Omega=S$ is pre-summed into $\hat Y(S)$ at the cost of $\kappa_0$ in the rate (as in the proof of Theorem 3.4), which we do only where stated.

*(a).* By P5 (3.14), (3.17) and P6 (4.35)–(4.36), $\mathscr E'^{(k+1)}_1(z)=\int_0^1ds\,\langle U_{s,0}(z)\rangle_{s,0}$, where $U_{s,0}(z;\sigma,\hat\psi)$ is (3.3) with $t=s$, $u=0$, the
$\delta\mathscr F$-term dropped and all scalar products restricted to $B_{k+1}(z)$, evaluated at $\sigma=1$. Its expansion $U_{s,0}(z)=\sum_{Y_0\ni z}U_{s,0}(z,Y_0)$ with
$|U_{s,0}(z,Y_0)|\le\varepsilon_Ue^{-\kappa_Ud^{\rm cov}(Y_0)}$ is the proof of Proposition 3.3 for one block (P6 (4.37)). Theorem 3.4 with $G=U_{s,0}(z,Y_0)$, $F_0=\varepsilon_U$, $\kappa_G=\kappa_U$ gives
$\langle U_{s,0}(z,Y_0)\rangle=\sum_SG^*(Y_0,S)$ with $|G^*|\le C_{\rm PE}\varepsilon_Ue^{-\kappa_0d^{\rm cov}(Y_0)}e^{-\kappa_ad_\Omega(S)}$; summing over $Y_0\ni z$ (Lemma 1.2 (G2)) gives
$\le C_{\rm PE}\varepsilon_UK_0e^{-\kappa_ad_\Omega(S)}\le K_0e^{-\kappa_ad_\Omega(S)}$ for $\beta$ large. The determinant: $D^{(k)}(z)=\sum_{y\in B(z)}\mathrm{tr}\,\mathbb L(y,y)$ is expanded by LOC V3
($F(s)=\mathbb L(s)(y,y)$, LOC I-4c (iii), (v)) and Lemma AE, with terms $\le NB_{\mathbb L}e^{-2\kappa d^{\rm cov}(Y)}$ (GM with $d_j(X)=0$); pre-summed to $\hat Y(S)$ and summed over $y\in B(z)$ this is
$\le\frac12NL^dB_{\mathbb L}K_0e^{-(2\kappa-\kappa_0)d_\Omega(S)}$, and $2\kappa-\kappa_0\ge\kappa_a$. Put $\mathscr E''^{(k+1)}_0(z,\hat Y(S)):=$ the sum of the two pieces with support $S$. The whole-torus statement is
the locality clause of Theorem 3.4 together with the one of Proposition 3.3: for $\hat Y(S)\subset\Omega''_{k+1}$ every ingredient (interaction terms with support in $S$, the mark, $\nu$
on $S$, $\mathbb L(s)$ on $S$) is the whole-torus one.

*(a′).* The cubes $\square\subset Z^c_k\cap\Omega^c_{k+1}$ (unit cubes of scale $k$) carry marks $U(\square,Y_0)$ with $Y_0\cap\Omega_{k+1}\ne\varnothing$ (a term with $Y_0\cap\Omega_{k+1}=\varnothing$ does not
depend on $\hat\psi$, and the AE terms of a function vanishing at $\hat\psi=0$ with $\hat\psi|_{Y_0}=0$ vanish; P6 p. 40). Summing $|G^*(\square,Y_0,S)|$ over $\square\subset Y_0$ and $Y_0$ with
$Y_0\cap\Omega\subset S$ costs $\sum_{b\in S}\sum_{Y_0\ni b}|Y_0|e^{-\kappa_0d^{\rm cov}(Y_0)}\le|S|\,C(L,M)K_0\le C(1+d_\Omega(S))$ (Lemma 1.2 (G1)), i.e. one unit of rate:
$\le C_{\rm PE}\varepsilon_UC\,e^{-(\kappa_a-1)d_\Omega(S)}\le e^{-\kappa_bd_\Omega(S)}$ (P6 (4.57): $2\kappa-4-7\kappa_0$).

*(b).* P6 (4.58)–(4.67) with our bookkeeping. By (2.9) and P5 (3.15), $\langle g,\mathscr M''^{(k+1)}_0(g)\rangle=\int_0^1dt\int d\mu_{1,t}\langle\partial_{\psi'}\mathscr F_k(\psi^{(k)}+\beta_k^{-1/2}tC^{1/2}\hat\psi,g),C^{1/2}\hat\psi\rangle$.
Split the integrand into the first-order part $\langle\partial_{\psi'}\mathscr F_k(\psi^{(k)},g),C^{1/2}\hat\psi\rangle$ and the remainder (P6 (4.58)).
*First-order part.* It is $\langle g,(H_kC^{1/2}m)\rangle$ with $m(y):=\int_0^1dt\,\langle\hat\psi(y)\rangle_{1,t}$ and $H_k$ the derivative at $\psi'=0$ of $\phi_k(\psi^{(k)}+\psi')+\sum_j\mathscr M^{(j)}(\psi^{(j)}_k(\psi^{(k)}+\psi'))$
(P6 (4.61)). The kernel $(H_kC^{1/2})(x,y)$ has an expansion $\sum_{Y'\ni x,y}h(x,y;Y')$, $|h|\le C_he^{-2\kappa d^{\rm cov}(Y')}$, $C_h:=B_5K_3(C_3c_7)^{-1}+16B_5K_0K_2K_3L^\alpha(\alpha\alpha_0)^{-1}c_9$ (P6
(4.62); I-4a, I-4c and AE, with Cauchy radii $r_0=C_3c_7/(B_5|\psi'|)$, $r_j\propto\xi_j^\alpha/(B_5|\psi'|)$). For $m(y)$ apply Theorem 3.4 with the mark $G=\hat\psi(y)$ ($F_0=p_1$, its label the
$\pi'_{k+1}$-cube of $y$, $\mathsf d=0$): $\langle\hat\psi(y)\rangle_{1,t}=\sum_SG^*(y,S)$ with $|G^*(y,S)|\le C_{\rm PE}p_1e^{-\kappa_ad_\Omega(S)}$ for all $|\sigma|<R_\sigma$. **At $\sigma=0$ every $G^*(y,S)$ vanishes:**
the interaction (3.3) vanishes, only the polymer of the mark survives, and its derivative is $\int\hat\psi(y)\,d\nu_{p_1}=0$ (the measure (2.5) is even). By the Schwarz lemma in $\sigma$
(P6 (4.63): "we use for the first time the fact that the measure $d\mu_{s,t}$ can be analytically extended in the parameter $\sigma$"),
$|G^*(y,S)|_{\sigma=1}\le R_\sigma^{-1}C_{\rm PE}p_1e^{-\kappa_ad_\Omega(S)}\le C\beta^{-\frac18+\alpha'}\eta^{\gamma-\frac{\alpha_1}2-\alpha'}e^{-\kappa_ad_\Omega(S)}$ ((1.1)). The products $h(x,y;Y')G^*(y,S)$ are resummed over the
connected unions $Y'\cup\hat Y(S)$ (they share the cube of $y$): rate $\min\{2\kappa-1,\kappa_a\}-\kappa_0-1=\kappa_b$ (entropy and one volume factor). With $\beta_k^{-1/2}\le2\beta^{-1/2}\eta^{\frac{d-2}2}$ and
$\alpha'=\frac{\alpha_1}4$ the contribution to $\beta_k^{-1/2}\mathscr M''^{(k+1)}_0(x,Y)$ is $\le C\beta^{-\frac58+\frac{\alpha_1}4}\eta^{\frac{d-2}2+\gamma-\frac34\alpha_1}e^{-\kappa_bd}\le\frac14\beta^{-1/4}(L^{-1}\eta)^{\frac{d-2}2+\gamma-\alpha_1}e^{-\kappa_bd}$
for $\beta$ large ($\eta\le1$).
*Remainder.* By P6 (4.59)–(4.60) its integrand has localized terms of size $\le C(1+c_9)\beta_k^{-1/2}p_1^2\big(1+\eta^{\min\{0,\,3\gamma-\alpha_1-\frac{d-2}2\}}\big)\le C\beta^{-\frac12+2\alpha'}\eta^{\gamma-2\alpha'}$ (the radii
$r_0,r_j$ as above; the $\mathscr M^{(j)}$-terms carry $r_j^{-2}c_9\xi_j^{\frac{d-2}2+\gamma-\alpha_1}\propto p_1^2\xi_j^{3\gamma-\alpha_1-\frac{d-2}2}$, and $\min\{\frac{d-2}2,3\gamma-\alpha_1\}\ge\gamma$ because $\alpha_1<\gamma/2$) and rate $2\kappa$; Theorem 3.4 (one mark) and the factor $\beta_k^{-1/2}$ of (3.11) give
$\le C\beta^{-1+\frac{\alpha_1}2}\eta^{\frac{d-2}2+\gamma-\frac{\alpha_1}2}e^{-\kappa_ad}\le\frac14\beta^{-1/4}(L^{-1}\eta)^{\frac{d-2}2+\gamma-\alpha_1}e^{-\kappa_ad}$. Adding the two parts gives (b). (Finding F-4: P6 (4.67) prints
$\eta^{\gamma-2\alpha_1}$ for the same quantity, which does not reach (H.7)'s $\eta^{\gamma-\alpha_1}$; the auxiliary exponent $\alpha'=\alpha_1/4$ in (1.1) repairs it.)

*(c).* P5 (3.2): $\mathcal B''^{(k+1)}=\int_0^1du\,\langle\mathcal B''^{(k)}\rangle''_u$, the measure with interaction $\mathscr U+u\mathcal B''^{(k)}$. Marks: the terms of the $\mathcal B''^{(k)}$-part of Proposition 3.3, $F_0=\beta_k^{-3/2}$,
labels $Y_0\in\mathcal D_{k+1}(\bmod\Omega^c)$ meeting $Z_k\subset\Omega^c_{k+1}$. Theorem 3.4 and the sum over $Y_0$: $\le C_{\rm PE}K_0\beta_k^{-3/2}e^{-\kappa_ad_\Omega(S)}\le\beta_k^{-1}e^{-\kappa_ad_\Omega(S)}$. Every label $\hat Y(S)\supset Y_0$
meets $\Omega^c_{k+1}$, and $S\ne\varnothing$. (P5 Prop 3.1's $\frac32\kappa$ is implied since $\kappa_a\ge\kappa_b\ge\frac32\kappa$ under (IC).)

*(d).* P5 (3.9): $\mathcal R'^{(k+1)}=\int_0^1du\langle\cdots\rangle'_u$ with marks the $\delta_0^{(k)}$-terms of Proposition 3.3, $F_0=\beta_k^{-m-2}$; Theorem 3.4 gives $\le C_{\rm PE}K_0\beta_k^{-m-2}e^{-\kappa_ad}$.
$-\delta D^{(k)}$ (P5 (2.41)): $\delta C^{(k)1/2}(\square')=\chi_{\square'}(C^{1/2}-C^{1/2}(\square',0))$ is $\le e^{-R_k}\le\beta_k^{-m-4}$ (P5 (2.34)), so its trace series localized by LOC V3 and AE is
$\le\beta_k^{-m-3}e^{-2\kappa d}$. Since $\beta_{k+1}\le2L^{d-2}\beta_k$, $C\beta_k^{-m-2}\le\frac12\beta_{k+1}^{-m-1}$ once $\beta_k\ge2C(2L^{d-2})^{m+1}$. **This resolves N-IV-1 of LFR (Lemma IV.1.8):** the
bound at scale $k+1$ holds because the construction delivers $\beta_k^{-m-2}$ (P6 Lemma 4.2: $\varepsilon=\mathrm{const}\,\beta_k^{-m-2}$), one power better than P5's printed $\frac12\beta_k^{-m-1}$. The
whole-torus clause: Theorem 3.4 locality.

*(e).* P5 (3.10)–(3.11): the marks are the $\mathcal R^{(k)}_n(X;\psi^{(k)}+\beta_k^{-1/2}C^{1/2}\hat\psi)$ with $X\cap\Omega_{k+1}\ne\varnothing$, localized by Proposition 3.3 ($F_0=\beta_k^{-n-1/2}$); those with
$X\cap\Omega_{k+1}=\varnothing$ do not depend on $\hat\psi$ and leave the expectation unchanged (P5 p. 518). Theorem 3.4: $\le C_{\rm PE}K_0\beta_k^{-n-1/2}e^{-\kappa_ad}\le\frac12\beta_{k+1}^{-n}e^{-\kappa_ad}$ for
$\beta_k^{1/2}\ge2C_{\rm PE}K_0(2L^{d-2})^n$. (P6 needs $\kappa-5-8\kappa_0\ge\frac12\kappa$ here; our condition is (IC).) $\square$

### 3.6 Proof of Theorem 3.1 (f)–(h): the renormalization expansions

We work after the scaling $S^{(k)}$ (scale-$(k+1)$ units; P4 (3.1)–(3.2), image p. 697). Unknowns $\xi=(\xi_1,\xi_2,\xi_3)$ (SF §3.1): $\zeta=\varepsilon_{k+1}\xi_1$, $\beta:=\beta_{k+1}$,
$\beta_u:=\beta_{k+1,u}=\beta_kL^{d-2}=\beta(1+\xi_3)$, free flow $a:=a_{k+1}=a_{k+1,u}$, $\nu_u:=\nu_kL^2$, $\nu:=\nu_{k+1}=\nu_u\frac{1+\xi_3}{1+\xi_2}$. For $\psi=\psi_{k+1}$ put $\theta=(1+\zeta)\psi$,
$A(\psi,\phi):=\frac a2\|\psi-Q\phi\|^2+\frac12\|\partial\phi\|^2+\frac\nu2\|\phi-h\|^2$, $A_u(\theta,\phi)$ the same with $(\theta,\nu_u)$; $\phi:=\phi_{k+1}(\psi)$, $\phi_u:=\phi_{k+1,u}(\theta)$ their backgrounds (in the $\nu$-free
convention without the $\nu$-terms in the variational problems), $\delta\phi:=\phi_u-\phi$, $\delta\alpha:=\alpha_u-\alpha$, $H_u:=-\Delta+aQ^*Q+\nu_u$ ($\nu$-free: without $\nu_u$).

**Lemma 3.5 (the renormalization identity at $\lambda=\infty$; P4 (4.2)–(4.16), P6 (2.22)–(2.24); proved).** (i) $\beta_uA_u(\theta,\phi_u)=\beta A(\psi,\phi)+\beta C^{(k+1)}$ with
$C^{(k+1)}=C_1-C_2+C_3$,
$$C_1:=\tfrac a2\xi_3\|\psi-Q\phi\|^2+(1+\xi_3)a\big(\zeta\langle\psi,\psi-Q\phi\rangle+\tfrac12\zeta^2\|\psi\|^2\big)+\tfrac12\xi_3\|\partial\phi\|^2+\tfrac12\nu\xi_2\|\phi-h\|^2,\qquad C_2:=\tfrac12(1+\xi_3)\langle\delta\phi,(H_u+\alpha_u)\delta\phi\rangle,$$
$C_3:=0$ in the complete convention and $C_3:=\nu(1+\xi_2)\big(\langle\delta\phi,\phi-h\rangle+\frac12\|\delta\phi\|^2\big)$ in the $\nu$-free one (P6 p. 11: "the additional term $\nu_{k+1}\langle\delta\phi_{k+1},\phi_{k+1}-h\rangle$").
(ii) $(\delta\phi,\delta\alpha)$ is the solution of BG Prop 5.1 (mode U) with $\phi_0=\phi$, $\alpha_0=\alpha$, lifted data $\delta\Psi=\zeta\psi$, mass $\nu_u$, and $f_1=(\nu_u-\nu)(h-\phi)$ (complete) resp.
$f_1=0$ ($\nu$-free); it is analytic in $(\psi,h,\xi)$, vanishes at $\xi=0$, and $\|\delta\phi\|_*+|\delta\alpha|_2\le3K_2\varepsilon_{k+1}|\xi|_\infty$ on $\Xi_{k+1}(1,\varepsilon_{k+1})$ for $|\xi|_\infty\le\frac1{16}$ (P4 (4.10)–(4.11)
at $\lambda=\infty$, where P4 has $7K_2$).
(iii) With $\psi^{(j)}_{k+1}:=$ `composeField`$(\mathbb B_j,\mathbb B_{k+1};\phi,\psi)$ and $\psi^{(j)}_{k+1,u}:=$ `composeField`$(\mathbb B_j,\mathbb B_{k+1};\phi_u,\theta)$ (same weights by the free flow),
$\delta\psi^{(j)}:=\psi^{(j)}_{k+1,u}-\psi^{(j)}_{k+1}$ is (6.2) applied to $(\delta\phi,\zeta\psi)$ (P4 (4.16)), affine in $(\delta\phi,\zeta\psi)$.
*Proof.* (i) $\beta^{-1}[\beta_uA_u(\theta,\phi)-\beta A(\psi,\phi)]=C_1$ by expanding $\|(1+\zeta)\psi-Q\phi\|^2$ and using $\beta_u=\beta(1+\xi_3)$, $\beta_ua=\beta a(1+\xi_3)$ (free flow), $\beta_u\nu_u=\beta\nu(1+\xi_2)$. Since
$\phi_u$ minimises $A_u(\theta,\cdot)$ on the sphere (complex data: is the small solution), the chord identity (LFR Lemma II.7.3; the algebra of Lemma 2.3 (a)) gives
$A_u(\theta,\phi)-A_u(\theta,\phi_u)=\frac12\langle\delta\phi,(H_u+\alpha_u)\delta\phi\rangle$. In the $\nu$-free convention the $\nu$-terms are not in the variational problem and their difference,
$\frac{\beta_u\nu_u}2\|\phi_u-h\|^2-\frac{\beta\nu}2\|\phi-h\|^2=\beta\big(\frac{\nu\xi_2}2\|\phi-h\|^2+C_3\big)$, is expanded directly. (ii) Subtract the two (EL) systems:
$(H_u+\alpha+\delta\alpha)\delta\phi+\delta\alpha\,\phi=aQ^*(\zeta\psi)+(\nu_u-\nu)(h-\phi)$, $(\phi+\delta\phi)\cdot(\phi+\delta\phi)=1$; this is (P-1)–(P-2). Sizes: $|\zeta\psi|\le\frac32\varepsilon_{k+1}|\xi_1|$,
$|\nu_u-\nu||h-\phi|\le2|\xi|\sqrt\nu\cdot\varepsilon_{k+1}$ on $\Xi_{k+1}$ (complete convention: $|\phi-h|<\varepsilon_{k+1}/\sqrt\nu$). (iii) (6.2) is affine in $(\phi',\Psi')$. $\square$

Then, as in P4 (4.17), (4.18), (4.20)–(4.22) (images pp. 703–705):
$$\mathscr E^{(k+1)}_u(\psi,h):=\mathscr E^{(k+1)}_0((1+\zeta)\psi,h)+\sum_{j\le k}\big[\mathscr E^{(j)}(\psi^{(j)}_{k+1}+\delta\psi^{(j)},h)-\mathscr E^{(j)}(\psi^{(j)}_{k+1},h)\big],\tag{3.10}$$
$$\mathscr M^{(k+1)}(\psi,h,g):=\beta_k^{-1/2}\mathscr M^{(k+1)}_0((1+\zeta)\psi,h,g)+\delta\phi+\sum_{j\le k}\big[\mathscr M^{(j)}(\psi^{(j)}_{k+1}+\delta\psi^{(j)},h,g)-\mathscr M^{(j)}(\psi^{(j)}_{k+1},h,g)\big],\tag{3.11}$$
the pre-localization of the differences by $\int_0^1dt\,\frac d{d\tau}(\cdot)\big((t+\tau\chi_{\Delta(z)})\text{sources}\big)|_{\tau=0}$ (P4 (4.20); $\sum_z\chi_{\Delta(z)}=1$ and the chain rule give back $\int_0^1dt\frac d{dt}$),
$E^{(k+1)}(z):=\mathscr E^{(k+1)}_u(z;e_1,e_1)-\beta C^{(k+1)}(z;e_1,e_1)$ (independent of $z$), and the new term $\mathscr E^{(k+1)}(z):=\mathscr E^{(k+1)}_u(z)-\beta C^{(k+1)}(z)-E^{(k+1)}(z)$ (P4 (4.22)).
The density after the step is P4 (4.21) at $\lambda=\infty$ (with $\lambda$- and $d$-terms absent).

*Proof of (g).* $C_1(z)$ (scalar products restricted to $B_{k+1}(z)$) depends on $\psi$ through $\phi=\phi_{k+1}(\psi)$; expand it by LOC I-4b (decoupled $\phi_{k+1}(s)$) and AE. On
$\Xi_{k+1}(1,\varepsilon_{k+1})$ each factor $\psi-Q\phi$, $\partial\phi$, $\sqrt\nu(\phi-h)$ is $O(\varepsilon_{k+1})$ (complex extension: $\Xi^c$, same order), and $|\zeta|\le\varepsilon_{k+1}\epsilon$, so
$|C_1(z,Y)|\le C_4'\varepsilon_{k+1}^2\epsilon e^{-2\kappa d^{\rm cov}(Y)}$. $C_2(z)$: $\delta\phi$ by LOC I-4a (mode U, the sources of Lemma 3.5 (ii), decoupled with the same $s$) and AE; quadratic, hence
$C_4'\varepsilon_{k+1}^2\epsilon^2$. $C_3(z)$ ($k+1\le k_0$): $\nu_{k+1}\le e^{2\epsilon}\beta_{k+1}^{-1}\le\varepsilon_{k+1}^2$, so it is $\le C\varepsilon_{k+1}^3\epsilon$. $\mathscr E^{(k+1)}_u(z)$: the first term of (3.10) is (a)
evaluated at $\theta=(1+\zeta)\psi$, which lies in the unrenormalized domain for $\psi\in\Xi^c_{k+1}(1,\varepsilon_{k+1})$ by (Ξ2) ($\delta_3\le\varepsilon_{k+1}\epsilon$) — this is P4's inclusion
$\Xi^c_{k+1}\subset\Xi^c_{k+1,u}$ (p. 697) —, so its expansion and bound are those of (a). The second term: write $\mathscr E^{(j)}$ through Lemma 3.2 (whole lattice: $\sum_X I$; subdomain: $\sum_XI^W$); the
$\tau$-derivative is bounded by Cauchy on $|\tau|=c_r/\epsilon$ (the sources then stay $\le c_r\varepsilon_{k+1}$, inside the margin of LOC (4.38)); the argument $\psi^{(j)}_{k+1}+\delta\psi^{(j)}$ lies in
$\mathcal S_j(X)$ ((R-S) applies to the affine formula (6.2)); I-5 (V0) — in the "simple variation" in which the perturbation is the source-driven decoupled $\delta\phi(s)$ of LOC I-4a
instead of the fluctuation (LOC V3) — and the resummation of Proposition 3.3 give $\le C_5E_0\epsilon\,e^{-(2\kappa-1)d^{\rm cov}(Y)}$ per $z$. Joint analyticity in $\xi\in\mathcal P_\epsilon$: the sources are affine in
$\xi$, I-4a is analytic in its data, and AE preserves joint analyticity. The subdomain form adds P6 (2.27)–(2.30): the pre-localization with the counterterm of P5 (1.8) and its
restoration (2.30), whose terms have $z\in(Z^c_{k+1})^\approx\cap Z_{k+1}$ and go to the boundary terms with the bounds of P1 (3.77), (3.80) [review] — cited. $\square$

*Proof of (h).* Term by term in (3.11): the first by (b) at $\theta=(1+\zeta)\psi$; $\delta\phi(x)$ by I-4a and AE, $\le3K_2\varepsilon_{k+1}\epsilon e^{-2\kappa d}$, and
$\varepsilon_{k+1}=\alpha_{0,k+1}\xi_{k+1}^{\frac{d-2}2+\gamma-\alpha_1}L^{(k+1)(2\gamma-\alpha_1)}$; the $\mathscr M^{(j)}$-differences by the Cauchy argument of (g) with the bound $c_9\xi_j^{\frac{d-2}2+\gamma-\alpha_1}$ of (H.7) and
no volume factor, summed over $j\le k$ (dominated by $j=k$). Together: $(\frac12\beta^{-1/4}+C_6\epsilon L^{(k+1)(2\gamma-\alpha_1)})\xi_{k+1}^{\frac{d-2}2+\gamma-\alpha_1}e^{-\kappa_bd}$, which is P4 Proposition 4.2. $\square$

*Proof audit of (f) [v2.1: FL-A03] (P6 (2.11)–(2.20), Props 2.1–2.2; VMOD §2).* Put $D=Z_k^c$, $D_+=Z_{k+1}^c$. There are two distinct background comparisons. P6 (2.12) compares the old mixed set $\mathbb B'_{k+1}=(\mathbb B_k(W_k)\cap\Omega^c_{k+1})\cup\Lambda_{k+1}$ with $\mathbb B_{k+1}(W_{k+1})$; its composed-data difference $\delta\theta'$ vanishes on $W_{k+1}$. P6 (2.16) compares $\mathbb B'_{k+1}$ with $\mathbb B_{k+1}(\partial\Omega_{k+1})$; that difference vanishes on $W_k\cap U_{k+1}$. BG composition and perturbation give these identities, conditional on the generating-set agreements of Lemma 2.8. Formally splitting summands by their localization point and old support with the P5 (1.8) counterterm restriction, then applying the fundamental theorem of calculus to the composed fields, gives the **algebraic** identity
$$\mathscr E_k(D;\psi'_u)=\mathscr E_k(D_+;\psi_u)+\mathscr E'_k(D\cap Z_{k+1};\psi'_u)+\sum_{j=1}^k\int_0^1\frac d{dt}\mathscr E^{(j)}\bigl(D_+;\psi_u^{(j)}+\delta\psi_u^{(j)}(t\delta\theta')\bigr)\,dt.\tag{3.12}$$
This is P6 (2.19), equivalently VMOD (2.2). It proves the identity only; it supplies neither a support nor a coefficient bound.

**The local I-6 input.** Lemma 3.2(ii)–(iv) already proves, conditional on the PROVED landed `Itw_congr`, `IW_congr`, `energyW_sub_AW_eq_tsum_IW` and their `PremisesTerm`/`SumConds` hypotheses, that an irrelevant summand reads $X\cup\operatorname{st}_+(y)$ (or $(X\cap W)\cup\operatorname{st}_+(y)$ after restriction). Equation (3.0) pays the fixed enlargement cost. Thus the *abstract* star-local algebra and covering-rate calculation requested by VMOD's OPEN-LOCAL-I6 are now available. Its **actual old-action instantiation remains OPEN**. Precisely, `PremisesTerm.ofDomain` requires an inclusion of its `Tube` in the class domain, whereas the landed draft Def-6 `IsSF.analyticE` supplies only `XiDom` analyticity; no such inclusion for the old H7 terms is established. Also the draft Def-6 `RenormCond.moment` asserts convergence of a family of torus moments to zero, while `SumConds.moment` requires an exact zero for its infinite-polymer tensor sum. The transfer between these carriers, and the other `PremisesTerm`/`SumConds` fields for the actual Def-7 terms, must be proved. One also needs a common open Cauchy neighbourhood and a check that the P5 (1.8) restriction distributes the counterterms exactly as (3.12) requires. The $j=k$ inherited-term argument needs agreement of the two composed data on $X^\star$, or a separate allocation of the star-crossing terms to the boundary sum. Merely $X\subset(\Omega_{k+1})^c$ does not ensure $X^\star\subset(\Omega_{k+1})^c$: take $y$ on its boundary, $y-e_\mu\in X$, and $y+e_\mu\in\Omega_{k+1}$; $\Phi_{y,X}$ then reads the latter site when its second-moment tensor is nonzero. This is a precise obstruction to applying P6's unchanged-$j=k$ sentence to the **termwise** irrelevant decomposition without a star-margin or cancellation argument.

**The old-background H7 estimate.** Here is the quantitative implication that can be proved. For either of P6's two comparisons suppose, on an open neighbourhood of the complex H7 domain and the closed decoupling polydisc, that the changed datum has norm at most $C_{\rm src}r_{H,k}$, vanishes on the appropriate set above, and the common-cover weighted response gives $\|w\|_*+\|\partial w\|_*+\|\Delta w\|_*+\|\delta\alpha\|_*\le C_{\rm resp}r_{H,k}e^{-\gamma_wD_{\rm old}}$ on the action support, where $w=\delta\phi$ and $D_{\rm old}$ is its actual collar distance. The H7 bounds put the first variations of the block, bond and surface terms at $O(r_{H,k})$. In the $\nu$-free convention the mass stays in $A^\star$ but is absent from its variational equation, so P6 (2.14) has the additional **linear** term $\nu_{k+1,u}\langle w,\phi-h\rangle$. To bound it by $Cr_{H,k}^2e^{-\gamma_wD_{\rm old}}$ one also needs $\nu_{k+1,u}|\phi-h|\le C_{\rm mass}r_{H,k}$ on that complex domain. The $\nu$-free H7 inequalities do **not** give this: their background has mass zero, so its regularity conditions impose no $h$-bound, while the action retains a positive mass coefficient. If $h$ is allowed to range over the unrestricted complex $\nu$-free H7 coordinates and $w\ne0$, the term grows linearly with $h$. A bounded complex neighbourhood of the physical $|h|=1$ sphere, or an explicit bound on $b=\nu_{k+1,u}h$, is therefore an additional necessary input. In the complete convention the mass belongs to the variational equation and this separate linear term is absent. The remaining P6 (2.14)/(2.17) quadratic and surface terms are bounded by $C(r_{H,k}|w|+|w|^2)$ after the sphere chord identity, so **under that extra mass-domain input in the $\nu$-free case**, per cube
$$\bigl|\beta_{k+1,u}\big(A^\star_D(\phi+w)-A^\star_D(\phi)\big)\bigr|\le C_{\rm old}\beta_{k+1,u}r_{H,k}^2e^{-\gamma_wD_{\rm old}}.\tag{3.13}$$
The factor $\nu\langle w,\phi-h\rangle$ is assigned to the **opposite convention** in VMOD §2.1; P6 (2.14), immediately after the display, says it disappears when the external field is included in the variational problem. In particular it is present for the old $\nu$-free action at $k=k_0$ before the switch. The step from the hypotheses in this paragraph to (3.13) is proved by expanding the quadratic action; the asserted complex source, mass-domain bound, common-cover response, collar and analyticity hypotheses themselves are **OPEN-OLD-H7-DECAY** in the present auxiliary geometry. The real $\delta_k$ cutoff and P6's real bound (2.13) do not supply them on H7.

The late absorption in (3.13) has no arithmetic obstruction. If both old collars satisfy the conservative $D_{\rm old}\ge M([R_{\rm base}(x-2)^2]-1)-2M_1$ for $x=\hat\lambda_k\ge\lambda_*$, then $\beta_{k+1,u}\le C_La^{-1}e^x$ and $r_{H,k}\le C_H\alpha_0$ give the sufficient condition
$$C_{\rm old}C_LC_H^2a^{-1}\alpha_0^2e^x\exp\{-\gamma_w[M([R_{\rm base}(x-2)^2]-1)-2M_1]\}\le e^{-R_{\rm base}x^2}.\tag{3.14}$$
The logarithm of its left/right ratio has quadratic coefficient $-(\gamma_wM-1)R_{\rm base}<0$ by the row-6 choice $\gamma_wM>1$. Therefore a finite late $\lambda_*^{\rm old}$ exists after $M,\alpha_0,E_0$ are fixed, and can be included in row 16. This proves the **conditional** $e^{-\hat R_k}$ absorption, since $\hat R_k=R_{\rm base}x^2$; the required collar lower bounds and H7 response remain OPEN.

Finally, (3.12) still needs the mixed-cover (Vmod) on open H7 neighbourhoods, the coarse halo of VMOD (1.1) for $j=k$, and the charged-cover/point resummations to reach the rate $2\kappa-\kappa_0-1$. `i5_background` has no fluctuation variable and does not give this. For the observable, P6 (2.10) supplies linearity in $\chi_Dg$, but its H7 and $\ell^1$ coefficient bound with constant $2$ must be checked independently; (3.13) is a scalar-action estimate. At $k=k_0$ the old action is $\nu$-free and the output uses complete variables, so the separate joint-$\xi$ switch remains OPEN-SWITCH-JOINT (RGFREE.md). These missing analytic and geometric assertions prevent a proof of P6 Props 2.1–2.2 in the present conventions; the algebra (3.12), star cost (3.0), conditional estimate (3.13), and scalar late comparison (3.14) are the parts closed here.

### 3.7 Exponents and the iteration condition

| Quantity | Rate (in $d^{\rm cov}_{k+1}$, mod $\Omega^c$ where relevant) | Origin of the loss |
|---|---|---|
| interaction $\mathscr U(Y)$ (Prop 3.3) | $\kappa_U=2\kappa-1$ | I-5 doubles $\kappa$ (GM4); $-1$ for $\sum_{z\in Y}$ |
| $\mathscr E''^{(k+1)}_0(z,Y)$, (a) | $\kappa_a=\kappa_U-3\kappa_0-c_1-\frac32$ | Theorem 3.4: pre-summation $\kappa_0$, MY $\kappa_0+\frac32$, PE-L $\kappa_0+c_1$ |
| $\mathcal B''^{(k+1)}$ (c), $\mathcal R'$ (d), (e) | $\kappa_a$ | Theorem 3.4 |
| $\mathscr E'^{(k+1)}_1$ off $\Omega$ (a′), $\mathscr M''^{(k+1)}_0$ (b) | $\kappa_b=\kappa_a-\kappa_0-1$ | one more resummation |
| renormalized new terms $\mathscr E^{(k+1)}$, $\mathscr M^{(k+1)}$ (g), (h) | $\ge\kappa_b$ | $C_i$, old-term changes at $2\kappa-1$ |
| P6 Props 2.1–2.2 boundary terms (f) | $2\kappa-\kappa_0-1$ (scale $k+1$), $\kappa-1$ (scale $k$, inside $\Omega^c_{k+1}$) | I-5 |
| background change $\Delta(Y)$ (§4) | $\frac32\kappa$ (any rate $\le2\kappa-1$) | AE with $\kappa_1\ge4d(2L+1)^d\kappa$ |

**(IC) (iteration condition).** The new terms must decay at least at P5 Theorem 1's rate $\frac32\kappa$ (LFR: $\kappa_+=\frac32\kappa$ in (D7) of the pre-class; Def-6 at $k+1$ needs $\kappa$): 
$$\kappa_b\ge\tfrac32\kappa\iff\kappa\ge7+8\kappa_0+2c_1 .$$
Since $\kappa_0\ge c_1$ by the choice of §1.2, (IC) is implied by $\kappa\ge7+10\kappa_0$, hence by LFR's $\kappa_{\rm flow}\ge16\kappa_0+16$ (D-IV.7); it also implies I-5's $\kappa\ge3\kappa_0+3$ and
$2\kappa-\kappa_0-1\ge\frac32\kappa$. For comparison: SF v3's condition $\kappa\ge8+14\kappa_0$ is the same statement with P6's losses ($2\kappa-4-7\kappa_0\ge\frac32\kappa$); P6's own Proposition 3.3
needs $\kappa\ge10+16\kappa_0$ ($\kappa-5-8\kappa_0\ge\frac12\kappa$, p. 43); with the sharpened PE-L ($c_1\to1$), (IC) reads $\kappa\ge9+8\kappa_0$. Old scales keep rate $\kappa$ (their terms
are only restricted), so the class is preserved with the same $\kappa$; the improvement to $\frac32\kappa$ concerns only the terms created by the step.

---
## 4. O-2′: the analytic half of Lemma F (LFR Lemma IV.1.3)

### 4.1 Decay of the response to a far data change

**Lemma 4.1 (far data changes; P3 Prop 2.1 (2.55)–(2.56) and P6 (2.13) at $\lambda=\infty$; conditional on the OPEN weighted decoupled NC input).** Let $\mathbb B$ be a generating set at
level $q$ (BG §1.1, separation $\varrho\ge R_0$), admissible weights, mass $0\le\mu\le L^{-2q}$, $(\Psi,h)\in\tilde\Psi^c(\mathbb B;\delta,\varepsilon)$ with $\delta\le c_1$ (BG Thm 5.2), and let
$\delta\Psi$ be a lifted data change supported in a set $W$ of blocks and collar sites, $|\delta\Psi|\le\delta_1\le\delta_*$, such that $(\Psi+\delta\Psi,h)$ is in the domain as well. Let
$(\phi,\alpha)$ and $(\phi+\delta\phi,\alpha+\delta\alpha)$ be the small solutions and $\mathrm d$ the path metric of GR §1.4 (scaled distance). Then for every $x\in\Omega_1$
$$|\delta\phi(x)|+\ell(x)|\partial\delta\phi(x)|+\ell(x)^2|\Delta\delta\phi(x)|+\ell(x)^2|\delta\alpha(x)|\le K_{\rm far}\,\delta_1\,e^{-\gamma_w\mathrm d(x,W)},\qquad\gamma_w=\gamma_0/4,\tag{4.1}$$
with $K_{\rm far}=K_{\rm far}(d,L,N)$. The same holds for the decoupled solutions of LOC I-4a (mode U or P, data change only, the decoupling vector $s$ fixed in the polydisc
$|s_P|\le e^{\kappa_1}$), with $K_{\rm far}$ replaced by $K_{\rm far}e^{N_0\kappa_1}$.

*Proof.* By BG Thm 5.2 (6), $(\delta\phi,\delta\alpha)$ is the solution of BG Prop 5.1 with $\phi_0=\phi$, $\alpha_0=\alpha$, the lifted data $\delta\Psi$, $f_1=0$, $g=0$. Its source
$F_s=Q^*a\,\delta\Psi+\mathfrak b(\delta\Psi)$ is supported within one block or one bond of $W$. Take the weight $w:=e^{\gamma_w\mathrm d(\cdot,W)}$; it belongs to LOC's class $W_{\gamma_w}$ (landed
`isWeight_of_dist`), and $|F_s|_{2,w}\le e^{\gamma_wdL}|F_s|_2\le e^{\gamma_wdL}\mathcal C_F\delta_1$. The proof of BG Prop 5.1 runs verbatim in the weighted norms $|\cdot|_{2,w}$, $\|w\,\cdot\|_*$:
the Green's function bound (G) holds in weighted form (GR G-2 (ii) summed with LOC's Lemma 4.4, landed `dirichlet_weighted`; LOC "weighted form of (NC3)" and (DG2) at
$s=1$), BG Lemmas 3.1–3.2 (the commutator $K$ and the remainder $R$) commute with $w$ up to the factor $e^{\gamma_w\rho_0}$ ($\rho_0=dL$, the range of a stencil and a block), and the
Lipschitz estimate (5.1) holds in the weighted norm with the same proof. So $\mathcal N$ is a $\frac12$-contraction of the weighted ball after decreasing $c_6,\delta_*$ by
$(d,L,N)$-factors; since $w\ge1$ its fixed point lies in the unweighted ball, hence equals $\delta\alpha$ (uniqueness), and $|\delta\alpha|_{2,w}\le2|\mathcal N(0)|_{2,w}\le C\delta_1$, whence (4.1)
for $\delta\phi=G(\alpha+\delta\alpha)(F_s-\delta\alpha\phi)$ by the weighted (G). The decoupled version is LOC I-4a Step 4 with the weighted (DG1)–(DG4) and the same source. $\square$

### 4.2 The theorem

Notation of LFR §II.2.3 and §II.5: at the step $k\to k+1$ ($k\ge0$), $Z'$ a component of $Z^{\rm pre}_{k+1}$, $X_{Z'}=Z^c_k\cap Z'$, $E_{Z'}=Z'^{\sim[\hat R_k]}$, $\mathbb B^\partial:=\mathbb B_{k+1}(\partial\Omega_{k+1})$
(P6 (2.15)), $\mathbb B^{\rm loc}:=\bigcup_{Z'}G^{Z'}_{k+1}$, $\tilde\psi$ the lifted multiscale data, $\phi^\partial:=\phi(\mathbb B^\partial;\tilde\psi)$, $\phi^{\rm loc}:=\phi(\mathbb B^{\rm loc};\tilde\psi)$ (LFR Definition II.2.7 (iv)),
$\mathcal A_{k+1}(Z';\psi)$ of LFR Definition II.5.4. $D_k:=M([\hat R_k]-1)-2M_1$.

**Theorem 4.2 (O-2′; [v2: FL-A04, FL-A05]; conditional on the OPEN decoupled cover/NC input of Lemma 2.8 and on the stated LOC I-4a/b hypotheses).** Work in the admissible step range $0\le\nu_{k+1}\le1$ (LFR Def-7 (D9), (D9$^\flat$)). Put $\varepsilon_{H,k}:=\max_{0\le j\le k+1}(\varepsilon_j+\varepsilon_{1,j})$, with $\varepsilon_{1,j}=(A_1/A_0)\varepsilon_j$ as in LFR §II.3.3, and $r_{H,k}:=\delta_k+\varepsilon_{H,k}$. The $j=0$ term covers the $\varepsilon_0$ radius of $\Delta'^c_1$ in H7 (1.36); every retained fluctuation is covered by $\varepsilon_{1,j}$ from (1.37). On the real support and on the complex H7 domain of LFR Definition II.3.5, the action difference has a local expansion. First put every term whose support $Y$ satisfies $Y\cap\Omega_{k+1}=\varnothing$ into $b_k$; such a connected $Y$ lies in one component of $\Omega_{k+1}^c$ and is an internal complement term. Its allocation to a $Z_{k+1}$ component uses the LFR region bookkeeping cited in §5.4. For the remaining terms,
$$\beta_{k+1}A^*_{k+1}\big(Z^c_k\cap Z_{k+1},\mathbb B_{k+1};\psi,\phi^\partial\big)=\sum_{Z'}\mathcal A_{k+1}(Z';\psi)+b_k+\sum_{\substack{Y\in\mathcal D_{k+1}(\bmod\Omega^c_{k+1})\\Y\cap\Omega_{k+1}\ne\varnothing}}\Delta(Y).\tag{4.2}$$
Each $\Delta(Y)$ depends only on the variables in $Y$, is analytic on an open H7 neighbourhood at $Y$, real on real arguments, $O(N)$-invariant and covariant under the Euclidean symmetries preserving $\pi_{k+1}$. With $D_k=M([\hat R_k]-1)-2M_1$,
$$|\Delta(Y)|\le C_F\beta_{k+1}r_{H,k}^{2}e^{-\gamma_wD_k}e^{-(2\kappa-1-\kappa_0)d^{\rm cov}_{k+1}(Y\bmod\Omega^c_{k+1})}\le e^{-\hat R_k/2}e^{-\frac32\kappa d^{\rm cov}_{k+1}(Y\bmod\Omega^c_{k+1})}.\tag{4.3}$$
The second inequality uses (IC) and the corrected (Λ28′) below. The first bound applies to complex H7 data. The real characteristic-function estimate is a separate bound and is not used in the complex Cauchy argument. Only the terms with $Y\cap\Omega_{k+1}\ne\varnothing$ enter the modular expansion and $\mathcal B^{(k+1)}$.

*Proof.* *Step 1 (the data change).* The generating-set nesting and BG Theorem 6.1 give the identity of the old Step 1, namely $\phi^\partial-\phi^{\rm loc}=\phi(\mathbb B^{\rm loc};\tilde\psi+\delta\Psi)-\phi(\mathbb B^{\rm loc};\tilde\psi)$, with $\delta\Psi=0$ on $E_{Z'}$. The vanishing uses only equality of the generating-set layers there (LFR Lemma II.2.5(c)) and therefore holds for every decoupling parameter. On the real support BG Theorem 6.1 and the characteristic functions give $|\delta\Psi|\le C\delta_k$. On complex H7 data the defining inequalities (1.36)–(1.37) of LFR Definition II.3.5 give the background-source norm $|\delta\Psi|+\nu_{k+1}|\delta h|\le C r_{H,k}$ (here the two constructions use the same $h$, so $\delta h=0$): the real H7 reference and complex displacement at each scale satisfy the $\varepsilon_j$ inequalities, and each retained fluctuation has size at most $\varepsilon_{1,j}$. The composition formula (6.2) is affine in these data and has bounded block averaging coefficients. This is the asserted complex estimate; the real cutoff is used only in the real estimate.

*Step 2 (weighted response).* Apply Lemma 4.1 to the source $\delta\Psi(s)$, which is zero on $E_{Z'}$. In the decoupling polydisc, the background difference, first differences and multiplier difference on $X_{Z'}^{+1}$ are bounded by $C K_{\rm far}e^{N_0\kappa_1}r_{H,k}e^{-\gamma_wD_k}$, since the distance from $X_{Z'}^{+1}$ to $E_{Z'}^c$ is at least $D_k$. This uses the decoupled I-4a/b bounds and their common cover. These bounds are conditional on the OPEN NC and new-interface cover conditions of Lemma 2.8; see notes/phase1/VMOD.md (in preparation).

*Step 3 (pre-localization).* Partition the restricted action into cubes $\square\subset X_{Z'}$ as in P5 (1.5), counting half bonds on the star once. For each $\square$ let $F_\square(s)$ be the difference of its action at $\phi^{\rm loc}(s)+\delta\phi(s)$ and at $\phi^{\rm loc}(s)$, multiplied by $\beta_{k+1}$. The coefficients of the first variation of the restricted action are bounded by $Cr_{H,k}$ on H7. For the block and kinetic terms this is the direct H7 bound on $\psi-Q\phi$ and $\partial\phi$: the H7 fields, including their real reference and complex increments, satisfy the $\varepsilon_j$ inequalities (1.36)–(1.37). For the mass term, the coefficient is $\nu_{k+1}(\phi-h)$, not $\sqrt{\nu_{k+1}}(\phi-h)$. The real reference condition inside the H7 domain gives $\sqrt{\nu_{k+1}}|\phi_r-h_r|\le C\varepsilon_{H,k}$, hence $\nu_{k+1}|\phi_r-h_r|\le C\varepsilon_{H,k}$ because $\nu_{k+1}\le1$; the H7 complex conditions give $|\phi_c-\phi_r|\le C\varepsilon_{H,k}$ and $\nu_{k+1}|h_c-h_r|\le C\varepsilon_{H,k}$. Thus $\nu_{k+1}|\phi_c-h_c|\le Cr_{H,k}$ even when $|h_c-h_r|$ itself grows as $\nu_{k+1}\downarrow0$. For the corresponding background change $w$, Step 2 gives $|w|+|\partial w|\le Cr_{H,k}e^{-\gamma_wD_k}$. Expanding each block or kinetic square by $Q(v+w)-Q(v)=2B(v,w)+Q(w)$, and the mass term by $\nu_{k+1}(\phi-h)\cdot w+\frac12\nu_{k+1}w\cdot w$, bounds every difference by $Cr_{H,k}^2e^{-\gamma_wD_k}$. There are at most $C(LM)^d$ such terms per cube. Thus $|F_\square(s)|\le C_F'\beta_{k+1}r_{H,k}^2e^{-\gamma_wD_k}$ uniformly on the complex H7 set and the decoupling polydisc. The surface first variation of P6 (2.14) is included in $2B(v,w)$; it has the same bound. I-4a/b and the affine composition make $F_\square$ holomorphic on an open neighbourhood of every closed parameter polydisc used by AE. The strict H7 inequalities and the strict numerical inclusions of §1.4 supply the data neighbourhood needed for Cauchy estimates.

*Step 4 (expand, then split the empty intersection).* AE and GM3–GM4 give $F_\square(1)=\sum_{Y\supset\square}F_\square(Y)$ with $|F_\square(Y)|\le C_F'\beta_{k+1}r_{H,k}^2e^{-\gamma_wD_k}e^{-2\kappa\tilde d^{\rm cov}_{k+1}(Y)}$. Before assigning a modular size, split this sum into $Y\cap\Omega_{k+1}=\varnothing$ and its complement. A connected support in the first part is inside one component of $\Omega_{k+1}^c$; summing its local coefficient into that component defines $b_k$. The ordinary entropy sum (G2) bounds the absolute sum there by $C\beta_{k+1}r_{H,k}^2e^{-\gamma_wD_k}$ times the number of its cubes, so $b_k$ has the required volume bound after (Λ28′). In the second part, $S=Y\cap\Omega_{k+1}$ is nonempty, $\hat Y(S)$ and $d_\Omega(S)$ are defined, and (G4) gives the comparison with the modular size. Pre-summing labels with the same $S$ costs $\kappa_0$ by (G2); summing $\square\subset Y$ costs one unit by (G1). This gives the first bound in (4.3). No modular expression is assigned to the empty-intersection terms.

*Step 5 (the late threshold).* For $\beta$ chosen after $\alpha_0,E_0$ as in §1.5, $\delta_k\le\varepsilon_0$ for every $k$; hence $r_{H,k}\le C_H\alpha_0$, since the $\varepsilon_j$ decrease and $\varepsilon_{1,j}=(A_1/A_0)\varepsilon_j$. Let $x:=\hat\lambda_k$ in the operative LFR flow (§I.3). Then $\hat R_k=R_{\rm base}x^2$ exactly, $\beta_{k+1}\le C_La^{-1}e^x$, and $D_k=M([R_{\rm base}x^2]-1)-2M_1\ge M([R_{\rm base}(x-2)^2]-1)-2M_1$ for $x\ge2$. Enlarge $C_F$ by $C_H^2C_L$ and impose the corrected late condition
$$\textbf{(Λ28′)}\qquad C_Fa^{-1}\alpha_0^2e^x\exp\{-\gamma_w[M([R_{\rm base}(x-2)^2]-1)-2M_1]\}\le e^{-R_{\rm base}x^2/2}\quad(x\ge\lambda_*).$$
It is checked after $L,\kappa_0,\kappa,\kappa_1,M,\alpha_0,E_0$ are fixed and before or with the final lower bound on $\beta$ (row 16). Indeed $[R_{\rm base}(x-2)^2]\ge R_{\rm base}(x-2)^2-1$, so the logarithm of the left/right ratio is at most $\log(C_Fa^{-1}\alpha_0^2)+x-\gamma_wM R_{\rm base}(x-2)^2+2\gamma_w(M+M_1)+R_{\rm base}x^2/2$. Its quadratic coefficient is $-(\gamma_wM-1/2)R_{\rm base}<0$ by the row-6 choice $\gamma_wM>1$. Thus a finite $\lambda_*$ exists, and the actual $x=\hat\lambda_k\ge\lambda_*$ satisfies the inequality. The exact identity $\hat R_k=R_{\rm base}x^2$ makes its right side $e^{-\hat R_k/2}$; this, together with $2\kappa-1-\kappa_0\ge3\kappa/2$ from (IC), proves the second bound of (4.3). Analyticity, reality and covariance follow from the corresponding properties of the decoupled backgrounds and AE. $\square$

**Corollary 4.3 (P6 (2.12)–(2.17); conditional on the same OPEN decoupled input as Theorem 4.2).** The background changes of P6 (2.12) ($\mathbb B'_{k+1}\to\mathbb B_{k+1}(W_{k+1})$ on $Z^c_{k+1}$) and (2.16) ($\mathbb B'_{k+1}\to\mathbb B_{k+1}(\partial\Omega_{k+1})$ on
$Z^c_k\cap Z_{k+1}$) produce, in the main action, terms with the expansion and bound of Theorem 4.2 (with $\hat R_k$ replaced by the margin of $W_{k+1}$, resp. of $W_k\cap U_{k+1}$); they are the
"very small" boundary terms of P6 p. 6 ("the bounds hold with constants smaller than any power of $\beta_k^{-1}$"). This supplies the first part of Theorem 3.1 (f).

### 4.3 What this changes in LFR

**[v2: FL-A04, FL-A05, FL-A13]** (i) O-2′ has the complex estimate (4.3) conditional on the OPEN decoupled cover/NC input and the stated LOC I-4a/b hypotheses; (Vmod) is not used (Step 4 compares
$\tilde d^{\rm cov}_{k+1}$ with the modular size directly: the layer-$(k+1)$ cubes of a chosen multiscale family form an admissible family of Definition 1.1, and $\ell_n^{-1}\ge1$); nothing of P6 §2 beyond (2.12)–(2.17) is cited. (ii) The rate
of $\Delta(Y)$ can be any $\kappa'\le2\kappa-1-\kappa_0$; LFR asks for $\kappa_+=\frac32\kappa$. (iii) (Λ28) should be read as the new (Λ28′), with the complex prefactor $C_Fa^{-1}\alpha_0^2e^x$ and the chosen distance $M[\hat R_k]$; it is eventually true in the order of §1.5. (iv) The size is $d^{\rm cov}_{k+1}(\cdot\bmod\Omega^c_{k+1})$ (LOC v3), weaker than P5's $d_{k+1}(\cdot\bmod\Omega^c)$; LFR's (D7) must be
stated with it (LOC v3 "Consequences for consumers" (2)).

---
## 5. I-9: one small-field step

### 5.1 Statements

**[v2: FL-A09, FL-A10, FL-A11]** The pointwise input is the amended Def-6/Def-7 (D2) class of §1.4, with local terms analytic on open neighbourhoods of $\Xi^c_j(\mathbb B_j(X);1,\varepsilon_j)$. The family input for a $\nu\downarrow0$ conclusion is the separate `ContAtZero` clause of the landed draft Def-6. The convention is $\nu$-free iff $j\le k_0$. "For $\beta$ large" means $\beta\ge\beta_*(\alpha_0,E_0)$ after fixing $\alpha_0,E_0$ and all earlier constants of §1.5.

**Theorem 5.1 (I-9, whole lattice; P4 Theorem 1 at $\lambda=\infty$).** Fix $d\ge3$, $N\ge2$, $L\ge3$, the constants of §1.5 in their order, and $\kappa$ satisfying (IC). There are
$\alpha_0^*>0$ and $E_0^*:=400C_4'B_6K_0K_5$ (Step 8; P4 (5.39) has $4C_4B_6K_0K_5$ with its constant $2$ in place of the landed $84$) such that **[v2: FL-A10]** for each fixed $0<\alpha_0\le\alpha_0^*$ and each fixed $E_0\ge E_0^*$ there is $\beta_*(\alpha_0,E_0)$, and with $c_9:=\beta^{-1/4}$, for $\beta\ge\beta_*(\alpha_0,E_0)$, $\bar\nu\le\frac78L^{-2}$ and every $k\ge1$:
$\chi_{k+1}S^{(k)}T^{(k)}\chi^{(k)}$ maps $\mathbb R^{\rm sf}_k(\beta,a,\nu;B,\bar\nu;\mathsf c)$ (convention of scale $k$) into $\mathbb R^{\rm sf}_{k+1}(\beta,a,\nu;BL^{d-2},\bar\nu L^2;\mathsf c)$ (convention of scale
$k+1$), and the new terms $\mathscr E^{(k+1)},\mathscr M^{(k+1)}$ satisfy (H.4), (H.7) with $\frac32\kappa$ in place of $\kappa$.

**Theorem 5.2 (the recursion; P4 Theorem 2 at $\lambda=\infty$).** In Theorem 5.1, $\mathscr E^{(j)}_{k+1}=\mathscr E^{(j)}_k$, $\mathscr M^{(j)}_{k+1}=\mathscr M^{(j)}_k$ for $j\le k$ (restricted to the new, smaller domains),
$$\beta_{k+1}=\frac{\beta_kL^{d-2}}{1+\xi^{(k)}_3},\qquad a_{k+1}=\frac{aa_k}{a_k+aL^{-2}},\qquad\nu_{k+1}=\nu_kL^2\frac{1+\xi^{(k)}_3}{1+\xi^{(k)}_2},\qquad z_{k+1}=1+\varepsilon_{k+1}\xi^{(k)}_1,\tag{5.1}$$
where $\xi^{(k)}$ is the unique solution in the polydisc of radius $r_0$ of the RG system of the step (SF §3.2 for $k\ge k_0$, SF §3.7 for $k<k_0$, the switch of Lemma 2.9 at
$k=k_0$), real for real data, analytic in every finite-dimensional analytic parametrization of the data (SF (L1)), and $|\xi^{(k)}|_\infty\le C_\xi\beta^{-1}L^{-2\gamma(k+1)}$; in the notation of
P4 (1.9), $b_{k+1}=\beta_{k+1}\xi_3$, $c_{k+1}=a_{k+1}b_{k+1}$, $e_{k+1}=\beta_{k+1}\xi_2$, and (1.10) holds with $c_8=4C_\xi/\beta$. The additive constants are $E_{k+1}=E'''_kL^d-E^{(k+1)}(0)$.

**Theorem 5.3 (the (F1) clause for families; [v2: FL-A09]; conditional on the OPEN step and $\nu$-free RG inputs named below).** Let $\nu\mapsto\rho_1(\nu)$, $0<\nu\le\nu_*$, be a family on a common torus and common localized-term indices. Assume each member belongs to the amended pointwise class of §1.4 with uniform constants, and assume the family satisfies the precise (CONT) clause `ContAtZero` of the landed draft `Balaban/SmallField/Def6.lean`: the relevant coefficients converge as $\nu\downarrow0$, and for each $j,y,X$ (respectively $j,x,X$) the functions $\mathscr E^{(j)}_\nu(y,X;\psi,b)$ (respectively $\mathscr M^{(j)}_\nu(x,X;\psi,b,g)$), with $b=\nu_jh$, converge uniformly on a nonempty $\nu$-independent open set $U$ lying in the corresponding $\Xi^c_j$ domain for all sufficiently small $\nu$. For the RG coefficient evaluations assume, in addition, that these common sets include fixed closed Cauchy polydiscs around the reference configurations, or that uniform analytic continuation from $U$ to those polydiscs has been established. This last working-neighbourhood condition is explicit because the bare `ContAtZero` declaration specifies only a nonempty open set.

For every flow generated by Theorem 5.1 from this family while $k<k_f(\nu)$, the pointwise bounds are $|\xi(\nu,k)|_\infty\le\frac{c_\xi}{4\beta}q^{k+1}$, $c_\xi=4C_\xi$, $q=L^{-2\gamma}$; $\beta_k=\beta L^{k(d-2)}\gamma_k$, $\nu_k=\nu L^{2k}\delta_k$; and $\gamma_\infty=\lim\gamma_k$ exists with $|\gamma_\infty-1|\le2C_\xi q/((1-q)\beta)$. The output family at every fixed $k$ satisfies `ContAtZero`, and $\lim_{\nu\downarrow0}\xi(\nu,k)$ exists. Set $\xi(\nu,k)=0$ for $k\ge k_f(\nu)$ or $\nu>\bar\nu$, and $\xi(0,k)=\lim_{\nu\downarrow0}\xi(\nu,k)$. The constants are independent of $\nu,k$ and the torus. The family conclusion is conditional on the OPEN actual $\nu$-free divided equations and $\varrho_{31}$; see notes/phase1/RGFREE.md (in preparation).

**Theorem 5.4 (subdomain form; the small-field part of P5 Theorem 1 / P6 Theorem 1 and Proposition 2.4; what LFR's LF-3 and LF-5 cite).** Let $\mathrm{IsRep}_k$ (resp.
$\mathrm{IsRep}^\flat_k$) hold with the hypotheses of Theorem 5.1, and fix a history and a step record. Then the exponent of P5 (3.18) is transformed into P6 (2.32):
$$\mathcal A_{k+1}(Z^c_{k+1})+\mathcal F_{k+1}(Z^c_{k+1})+\sum_{n<m}\mathcal R^{(k+1)}_n(Z^c_{k+1})+\mathcal R'^{(k+1)}_m(Z^c_{k+1})-\beta_{k+1}A^*_{k+1}(Z^c_k\cap Z_{k+1},\mathbb B_{k+1};\psi,\phi^\partial)+\mathcal B^{(k)}(Z^c_k\cap Z_{k+1})-(\text{vacuum constants})+\mathcal B^{(k+1)}(Z_{k+1}),$$
where the small-field data at scale $k+1$ satisfy Def-7 (D2) (new terms at rate $\frac32\kappa$; $\mathcal R'^{(k+1)}_m$ with $\frac12\beta_{k+1}^{-m-1}$), $\mathcal B^{(k+1)}$ satisfies (D7) with
$\kappa_+=\frac32\kappa$ and a constant $B_{\rm st}$ that depends on rows 0–11 (including $E_0$) but not on $B_0,H_0,c_1,c_2$, and $|\mathcal B^{(k)}(Z^c_k\cap Z_{k+1})|\le C_b(B_0+1)(|Z^c_k\cap\Omega^c_{k+1}|_\eta+|Z_{k+1}\cap\Omega_{k+1}|)$
(P6 (2.33)), analytic and covariant, depending on the variables in $U^\sim_{k+1}$.

**Status [v2.1: FL-A03, FL-A13].** Theorems 5.1 and 5.2 are **conditional on OPEN assertions**: the actual fluctuation/cover localization of Proposition 3.3, NC, the $\nu$-free coefficient $\varrho_{31}$ and divided equations, and the switch's joint $\xi$ estimates. See notes/phase1/VMOD.md and notes/phase1/RGFREE.md (in preparation). The landed `rg_step_infty` is a PROVED abstract theorem, but its premises have not been established for this step. Theorem 5.3 is a family statement whose preservation argument is proved under its working-neighbourhood hypothesis and those same OPEN step/RG assertions. Theorem 5.4 is **conditional on OPEN assertions** (Vmod), Theorem 3.1(f), the auxiliary cover/NC, the $\nu$-free H7 mass-domain input of §3.6, and the cited P1 (3.77), (3.80) bounds and P5 §2 bookkeeping; see notes/phase1/VMOD.md §2. None of these is a proved complete I-9 step.

### 5.2 Proof of Theorems 5.1 and 5.2

*Step 0 (data).* By (H.6) at $k$, $\beta_k\in[\frac12,2]\beta L^{k(d-2)}$, $\beta_k^{-1}\varepsilon_k^{-2}\le\frac2{\alpha_0^2}\beta^{-1}L^{-2\gamma k}$, and $\nu_k\le\bar\nu$.
*Step 1 (the Gaussian step).* Definition 2.1; on $\{\chi_{k+1,u}=1\}$ the data $(\theta,h)$ lie in $\tilde\Psi_{k+1}(4L\delta_k)$ (P4 (2.3) from $\chi_k$ and $\chi_{(2.2)}$, via P1 Lemma 3.1 = SF (D1)), and
Lemma 2.2 gives the unique minimiser $\psi^{(k)}(\theta)$ and (2.2).
*Step 2 (expansion, covariance).* Lemmas 2.3, 2.4; in the $\nu$-free convention with $V^{(k)}_\nu$ (D-FL.1).
*Step 3 (the fluctuation integral).* Lemma 2.5 and Proposition 2.6 give (2.6).
*Step 4 (its expansions).* Theorem 3.1 (a), (b) in the whole-lattice case: $\mathscr E^{(k+1)}_0(z)$ and $\mathscr M^{(k+1)}_0(x)$ have localization expansions with constants $(NL^dB_{\mathbb L}+1)K_0$ and
$\frac12\beta^{-1/4}$, rates $\kappa_a$, $\kappa_b$, analytic on $\Xi^c_{k+1}$ of the unrenormalized variable.
*Step 5 (scaling).* P4 (3.1)–(3.2): $\beta_{k+1,u}=\beta_kL^{d-2}$, $a_{k+1,u}=a_{k+1}$, $\nu_{k+1,u}=\nu_kL^2$; the old terms keep (H.2)–(H.5), (H.7) with the unrenormalized $\psi^{(j)}_{k+1,u}$ and the
domains $\Xi^c_{j,u}(1,\varepsilon_{j,u})$, $\varepsilon_{j,u}=\varepsilon_j+k^{-2}\alpha_0\xi_j^\alpha$ (P4 p. 697 [image]). At $k=k_0$ apply Lemma 2.9 now (switching term and re-expression added to $\mathscr E_0$, $\mathscr F_0$).
*Step 6 (renormalization).* Lemma 3.5 for every $\xi$ in the polydisc $\mathcal P_\epsilon$: the density equals P4 (4.21) at $\lambda=\infty$, i.e.
$\chi_{k+1,u}\exp[-\beta_{k+1}A_{k+1}(\psi_{k+1},\phi_{k+1})+\sum_{j\le k}\mathscr E^{(j)}(\psi^{(j)}_{k+1})+\sum_z\{\mathscr E^{(k+1)}_u(z)-\beta_{k+1}C^{(k+1)}(z)-E^{(k+1)}(z)\}-E_{k+1}|T^{(k+1)}_1|+\mathscr F_{k+1}]$ with
$\mathscr F_{k+1}=\langle g,\phi_{k+1}\rangle+\sum_{j\le k}\mathscr F^{(j)}(\psi^{(j)}_{k+1})+\langle g,\mathscr M^{(k+1)}\rangle$ (P4 (4.21) [image p. 705]); Theorem 3.1 (g), (h) expand the new functions jointly in $\xi$.
*Step 7 (the equations; [v2: FL-A07, FL-A08], conditional on OPEN inputs).* The renormalization conditions (H.5) for $\mathscr E^{(k+1)}$ have the complete divided system of SF §3.2 or the $\nu$-free system of SF §3.7. The first condition fixes $E^{(k+1)}(z)$. The landed `matrixFree` accepts an external $\varrho_{31}$ with a bound; it does not compute the coefficient of this fluctuation integral. At the switch, the added re-expression terms depend on $\xi$ and cannot be declared absent from the derivative matrix. See notes/phase1/RGFREE.md (in preparation) for both calculations. Only after that OPEN assertion supplies the actual `TriangularBounds`, the analytic divided data and the scale-sensitive `hηbd` may one apply the PROVED abstract `rg_step_infty` to obtain $|\xi^{(k)}|_\infty\le C_\xi\beta^{-1}q^{k+1}$. The bounds in Step 8 are conditional on this application.
*Step 8 (the hypotheses at $k+1$).* With $\epsilon:=|\xi^{(k)}|_\infty$:
- (H.1): multiply by $\chi_{k+1}$ and use Lemma 5.5; analyticity domains: Lemma 5.6 for the old terms, Theorem 3.1 (g) for the new ones.
- (H.2): the structure is that of Step 6 ($\psi^{(j)}_{k+1}$ is `composeField` of the renormalized background, Lemma 3.5 (iii)).
- (H.3): every construction is equivariant and the RG solution depends only on invariant data.
- (H.4): $\mathscr E^{(k+1)}(z,Y)=\mathscr E^{(k+1)}_u(z,Y)-\beta_{k+1}C^{(k+1)}(z,Y)-E^{(k+1)}(z)\mathbf 1[Y=B_{k+1}(z)]$. The landed `rg_step_infty` gives
$\epsilon\le84\eta$ with $\eta=B_6K_5\beta_{k+1}^{-1}\varepsilon_{k+1}^{-2}$ (P4 (5.31) has $2\eta$), hence $\beta_{k+1}\varepsilon_{k+1}^2\epsilon\le84B_6K_5$ and, by Theorem 3.1 (g),
$\beta_{k+1}|C_1(z,Y)|\le84C_4'B_6K_5e^{-\kappa_ad}$, $\beta_{k+1}|C_2(z,Y)|\le84C_4'B_6K_5\epsilon e^{-\kappa_ad}$, $|\mathscr E^{(k+1)}_u(z,Y)|\le B_6K_0e^{-\kappa_ad}$ (using $C_5E_0\epsilon\le1$),
$|E^{(k+1)}(z)|\le B_6K_0+170C_4'B_6K_5$ (P4 (5.35)–(5.37) [image p. 718]); so $|\mathscr E^{(k+1)}(z,Y)|\le E_0^*e^{-\kappa_ad^{\rm cov}(Y)}\le E_0e^{-\frac32\kappa d^{\rm cov}(Y)}$ with
$E_0^*:=400C_4'B_6K_0K_5$ ($C_4',K_0,K_5\ge1$) and (IC). The condition $C_5E_0\epsilon\le1$ is $168C_5E_0B_6K_5\alpha_0^{-2}\beta^{-1}\le1$, the analogue of P4 (5.41), the strongest
restriction on $\beta$.
- (H.5): by construction (Step 7); the conditions are imposed on the infinite-volume limits of the pre-localized functions, which exist by torus independence (PE (f), §3.4 locality).
- (H.6): $\beta_{k+1},\nu_{k+1}$ by (5.1); the landed `norm_xi_le_of_step` turns the step bound into $|\xi^{(k)}|\le\frac{c_8}4q^{k+1}$ for all $k$ with $c_8=4C_\xi/\beta$, and
`norm_gammaSeq_le` gives $\gamma_{k+1}^{\pm1},\delta_{k+1}^{\pm1}\le\exp(c_8\sum_jq^j)$.
- (H.7): Theorem 3.1 (h) with $\epsilon$: $\frac12\beta^{-1/4}+C_6C_\xi\beta^{-1}L^{-\alpha_1(k+1)}\le\beta^{-1/4}=c_9$ (P4 (5.40)).
- Coefficient ranges: $\beta_{k+1}>BL^{(k+1)(d-2)}$ from (H.6); $\nu_{k+1}\le\bar\nu L^2e^{c_8}$ (the class at $k+1$ is stated with the a priori bound of (H.6), the step hypothesis $\nu_{k+1}\le\frac78L^{-2}$
being checked by the caller: LFR uses $k<k_f$).
The recursion (5.1) is SF (3.1)'s change of variables; $c_{k+1}=a_{k+1}b_{k+1}$ is the free flow. $\square$

**Lemma 5.5 ($\chi_{k+1}\chi_{k+1,u}=\chi_{k+1}$; P4 p. 718; proved).** For $\beta$ large, $\chi_{k+1}(\psi_{k+1})=1$ implies $\chi_{k+1,u}((1+\zeta^{(k)})\psi_{k+1})=1$.
*Proof.* $\chi_{k+1}$ is the indicator of $\Xi_{k+1}(1,\delta_{k+1})$ in scale-$(k+1)$ units; in $\eta$-units its derivative conditions read $|\partial^\eta\phi_{k+1}|<L^{-1}\delta_{k+1}$,
$|\Delta^\eta\phi_{k+1}|,|\alpha_{k+1}|<L^{-2}\delta_{k+1}$, and $\delta_{k+1}\le2L^{-\frac{d-2}2}\delta_k$; the unrenormalized $\phi_{k+1,u}=\phi_{k+1}+\delta\phi$ with $|\delta\phi|$-norms $\le3K_2\varepsilon_{k+1}\epsilon\ll\delta_k$
(Lemma 3.5 (ii)); $|\theta-Q\phi_{k+1,u}|\le|\psi_{k+1}-Q\phi_{k+1}|+|\zeta||\psi|+|Q\delta\phi|<\delta_{k+1}+C\varepsilon_{k+1}\epsilon<\frac32\delta_k$; the $h$-condition likewise with $\nu_{k+1}\approx\nu_kL^2$. Each condition of $\chi_{k+1,u}$ (Lemma 2.5)
holds since $L\ge3$. $\square$

**Lemma 5.6 (the domain inclusion P4 (4.19); P4 p. 704 defers its proof; proved).** If $\psi^{(j)}_{k+1}(\psi_{k+1})|_X\in\Xi^c_j(\mathbb B_j(X);1,\varepsilon^{(k+1)}_j)$ then
$\psi^{(j)}_{k+1,u}((1+\zeta)\psi_{k+1})|_X\in\Xi^c_j(\mathbb B_j(X);1,\varepsilon^{(k)}_j)$ for $|\xi|\le\epsilon\le C_\xi\beta^{-1}L^{-2\gamma(k+1)}$ and $\beta$ large; here $\varepsilon^{(k)}_j=\alpha_{0,k}\xi_j^\alpha$ is the radius used at step $k$.
*Proof.* $\varepsilon^{(k)}_j-\varepsilon^{(k+1)}_j=\alpha_0k^{-2}\xi_j^\alpha$. The change $\delta\psi^{(j)}$ is (6.2) applied to $(\delta\phi,\zeta\psi)$ (Lemma 3.5 (iii)), of size $\le C(K_2+1)\varepsilon_{k+1}\epsilon$ in the norms of
BG Prop 5.1; by (Ξ2) (LOC §4.0) the perturbed configuration lies in $\Xi^c_j(\mathbb B_j(X);1,\varepsilon^{(k+1)}_j+(K_2+1)C(K_2+1)\varepsilon_{k+1}\epsilon)$, and
$C'\varepsilon_{k+1}\epsilon\le C'C_\xi\alpha_0\beta^{-1}L^{-(\alpha+2\gamma)(k+1)}\le\alpha_0k^{-2}L^{-\alpha j}$ for all $j\le k$ once $\beta\ge C'C_\xi\sup_kk^2L^{-2\gamma(k+1)}$. $\square$

**Lemma 5.7 ((B1) of SF; P4 (5.15)–(5.25) with $d^{\rm cov}$; proved).** Let $f_u(u,v,w)$ be the effective potential (per unit block, infinite volume) of $\mathscr E^{(k+1)}_u$ in the invariants of
SF §2.3 Step 3, $c_2$ that of $C_2$, and $v^{(k+1,\infty)}_u$, $v^\infty(C_2)$ their transversal second moments (P4 (5.15)). On $\mathcal P_{c_{10}}$ they are analytic in $\xi$, and with
$K_5:=9K_0(16dK_1LM)^2((2L+3)M)^d$: $|c_i(\xi)|\le K_5C_4'\epsilon^2$ on $|\xi|\le\epsilon\le c_{10}$, and the data of the divided system satisfy $|f_i(\xi)|\le B_6K_5\beta_{k+1}^{-1}\varepsilon_{k+1}^{-2}$ (P4 (5.24)–(5.25)).
*Proof.* P4 (5.15)–(5.17) [image p. 712]: the terms $\mathscr E^{(k+1)}_u(z,Y;e_1+\zeta e_2,e_1)$ are analytic in $\zeta$ on $\{|\zeta|<\frac12\delta_0\}$, $\delta_0=\frac12K_1^{-1}\varepsilon_{k+1}$ (P1 Lemma 3.2 = SF (D2): the
constant-plus-small configurations lie in $\Xi^c_{k+1}(1,\varepsilon_{k+1})$), so the second derivative in (5.15) is $\le(4/\delta_0)^2B_6e^{-\kappa_ad^{\rm cov}(Y)}$; $x_1^2\le|x-z|^2$ and Lemma 1.2 (G5) give
$|x-z|\le M(d^{\rm cov}(Y)+2\sqrt dL)$ in place of P1 (3.54); the sum over $z\in Y$ is $\le((2L+3)M)^d(1+d^{\rm cov}(Y))$ (G1); so the sum over $Y\ni0$ is $\le K_0$ provided $\kappa_a-3\ge\kappa_0$, which
(IC) implies. This gives $|v^{(k+1,\infty)}_u|\le2K_0(16dK_1LM)^2((2L+3)M)^dB_6\varepsilon_{k+1}^{-2}$, and the same with $C_4'\varepsilon_{k+1}^2\epsilon^2$ for $C_2$ (Theorem 3.1 (g)). The potentials $f_u$, $c_i$ and their
derivatives at $(1,\nu_{k+1},0)$ are bounded by Cauchy on the polydisc of SF Step 3. Dividing as in SF §3.4 gives (5.24)–(5.25). The bounds are uniform in $\nu\in(0,1]$ because the
$b$-variable domain does not depend on $\nu$ (SF §3.5, S-11). $\square$

### 5.3 (CONT) and the proof of Theorem 5.3

**Lemma 5.8 ((CONT) is preserved; [v2: FL-A09]; proved conditional on the OPEN step/RG inputs and the working-neighbourhood hypothesis of Theorem 5.3).** Suppose the scale-$k$ family satisfies the hypotheses of Theorem 5.3 through $k$, and the step maps each pointwise member to the amended scale-$(k+1)$ class. Then the output family satisfies the exact `ContAtZero` clause and $\xi^{(k)}(\nu)$ converges.

*Proof.* Fix $k$ and restrict to $0<\nu\le\nu_*(k+1)$. Every scale through $k+1$ is in the $\nu$-free convention (LFR D-IV.11), so the generating sets and the formulas for the backgrounds have a common domain; their weights $a_j(\nu)$ can still vary with $\nu$. The coefficients $\beta_j(\nu),a_j(\nu),\nu_j(\nu)$ converge by the induction hypothesis and the recursion; $\nu_j(\nu)\to0$. On a smaller common data neighbourhood, the uniform contraction used in BG Theorem 5.2 shows that the $\nu$-free background fixed points converge with their weights: if $T_{a,D}$ is the contraction, $\|\phi_{a,D}-\phi_{a_0,D_0}\|\le(1-q_{\rm BG})^{-1}\|T_{a,D}(\phi_{a_0,D_0})-T_{a_0,D_0}(\phi_{a_0,D_0})\|$, and the right side tends uniformly to zero because the finite-volume equations depend continuously on $(a,D)$. The same argument applies to the multiplier and, by Cauchy's formula, their derivatives on smaller closed polydiscs. Write the old local terms in $(\psi,b=\nu_jh)$ coordinates. Uniform convergence on the common working polydiscs and Cauchy's formula give uniform convergence of every derivative needed in the AE and RG coefficients on smaller fixed polydiscs.

The AE coefficients are finite sums of contour integrals of these derivatives against analytic background maps, so they converge uniformly there. For a Mayer coefficient, the finite cluster truncations converge by dominated convergence: the truncated Gaussian density has a cutoff $p_1(\beta_k(\nu))$ converging with $\beta_k(\nu)$; its indicator converges off the sphere $|\hat\psi_x|=p_1(\beta_k(0^+))$, a set of Gaussian measure zero. All products are bounded by the same small activity majorant of Theorem 3.4, and its entropy sum is independent of $\nu$; the tail is uniformly summable. Taking first the $\nu$ limit of a finite truncation and then the uniformly small tail proves uniform convergence of the full coefficient on the smaller common open polydisc. Its bound and holomorphy pass to the limit. Compositions with the old terms and backgrounds preserve this property.

For the RG solution, the coefficient functions and their first derivatives on the closed contraction ball converge by the preceding Cauchy argument. The actual $\nu$-free matrix and divided data are assumed to satisfy the uniform triangular and scale bounds assigned to notes/phase1/RGFREE.md (in preparation). The PROVED `tendsto_rg_solution` (or the elementary inequality $|\xi_\nu-\xi_0|\le2\sup_{\xi}|T_\nu(\xi)-T_0(\xi)|$ for half contractions) then gives $\xi^{(k)}(\nu)\to\xi^{(k)}(0^+)$. Formula (5.1) gives the new coefficients, and analytic composition gives the new local terms. Their convergence on a common smaller nonempty open set and the pointwise amended class bounds are exactly `ContAtZero` at scale $k+1$. $\square$

*Proof of Theorem 5.3.* Induct on $k$ using Theorem 5.1 for the pointwise estimates and Lemma 5.8 for the family clause. The initial family condition is an input; for the physical base family LFR Theorem II.7.10(e) is the cited base assertion and its compatibility with the amended domain must be checked. The PROVED abstract `rg_flow_infty` gives the stated $\gamma_\infty$ bound once its numerical hypothesis $6C_\xi q\le\beta(1-q)$ is imposed in the final $\beta_*$ choice. The convention at $k_f$ is a definition. Every use of Theorem 5.1, and therefore the family preservation in this application, remains conditional on the OPEN inputs identified in its status paragraph. $\square$

### 5.4 Proof of Theorem 5.4 (subdomain form)

Follow P5 §2–§3 and P6 §2 with the following inputs at each place. (1) P5 (2.1)–(2.16): decompositions and domains (cited; LFR Parts I–II). (2) P5 (2.17)–(2.41): the
substitution and the main action at $\lambda=\infty$ (§2.7; Lemmas 2.2–2.5 on the subdomain, the Jacobian with $D^{(k)}$, $\delta D^{(k)}$). (3) P5 (2.42)–(2.48): characteristic functions (LFR
Lemma IV.1.2). (4) P5 (3.1)–(3.18): Theorem 3.1 (a)–(e). (5) P6 (2.1)–(2.10): the new small-field region $Z^c_{k+1}$ (P6 (2.3)–(2.7)); the expansions of $\mathscr E''_0$, $\mathscr F''_0$, $\mathcal R'_n$
are split by the position of the localization domain: domains inside $(Z^c_{k+1})^\approx$ (resp. $Z^c_{k+1}$ for $\mathcal R$) form the small-field functions, by the whole-torus clauses of Theorem
3.1 (a), (d) these are the localizations of the whole-torus functions (P6 p. 3, "the crucial property"); the rest goes to $\mathcal B''^{(k+1)}$, with rates $\ge\kappa_b\ge\frac32\kappa$. (6) P6
(2.11)–(2.17): Theorem 4.2 and Corollary 4.3; **[v2: FL-A05]** its $Y\cap\Omega_{k+1}=\varnothing$ part is the internal $b_k$ contribution, allocated to $\mathcal B^{(k)}$ under the LFR component bookkeeping, while only $Y\cap\Omega_{k+1}\ne\varnothing$ enters the modular $\mathcal B^{(k+1)}$ expansion. (7) P6 (2.18)–(2.20) and Props 2.1, 2.2: Theorem 3.1(f), **[v2.1: FL-A03]** conditional on the open old-term, H7 and mixed-cover inputs listed in §3.6 and notes/phase1/VMOD.md §2. (8) P6 (2.21)–(2.29): Lemma 3.5 restricted to $Z^c_{k+1}$ (the counterterm is
pre-localized in blocks, (4.15)), the RG system solved for the whole-torus functions (P6 p. 3: "we have to take the thermodynamic limits"; the same $\xi^{(k)}$ as in Theorem 5.2),
Theorem 3.1 (g), (h). (9) P6 (2.30): the counterterm of P5 (1.8) for the new term is subtracted and added; by antisymmetry its added copy is a sum over
$z\in(Z^c_{k+1})^\approx\cap Z_{k+1}$, $y\in Z^c_{k+1}$, a boundary term with the decay of $v^{(k+1)}_1,v^{(k+1)}_2$ (P1 (3.77), (3.80), cited). (10) P6 (2.31): the renormalization of the main action on
$Z^c_k\cap Z_{k+1}$, with $\delta\phi_{k+1}(\partial\Omega_{k+1})$ from Lemma 3.5 (ii) for $\mathbb B_{k+1}(\partial\Omega_{k+1})$; its counterterm and surface term are bounded by const$\cdot$volume and go into
$\mathcal B^{(k)}$ (no expansion needed: they depend on the variables in $W^\sim_k\cap U^\sim_{k+1}$). (11) Bounds of the boundary terms: every contribution to $\mathcal B^{(k+1)}$ comes from Theorem
3.1 (a′), (c), (f), Theorem 4.2, item (9) or the surface terms of P6 after (2.25), with constants of rows 0–11; the old $\mathcal B''^{(k)}$ enters only through Theorem 3.1 (c), where $B_0$ is
absorbed by $e^{-\kappa R_k/2}$ (Proposition 3.3; LFR Lemma IV.1.5 (iii) and (Λ28)); hence $B_{\rm st}$ is independent of $B_0,H_0,c_1,c_2$. The old $\mathcal B'^{(k)}$ (domains in $\Omega^c_{k+1}$) goes
unchanged into $\mathcal B^{(k)}(Z^c_k\cap Z_{k+1})$, which gives the factor $B_0$ in (2.33). $\square$

### 5.5 Remarks on the base case, the last step, and the observable layer

*Base case (LFR O-IV-1, Proposition II.7.9).* At $k=0$ there are no old terms, the interaction consists of the chart terms of LFR Lemma II.7.4 (site-local, analytic for $|\xi|\le\frac12$) and,
in regime (A), the explicit field term; the covariance is $C^{(0)}=(P^\perp G^{-1}_\alpha P^\perp+P)^{-1}$ (GR §4.4 (ii)), and after $v=C^{(0)1/2}\hat\psi$ the measure is again the product (2.5). Proposition
3.3 then needs only the $V$-part (with the chart terms in place of $V^{(0)}$) and the localization of $C^{(0)1/2}$, and Theorem 3.4 applies unchanged; the renormalization at $k=0$ is §3.6
with $\mathscr E^{(j)}=0$. So the analytic part of O-IV-1 reduces to the analogue of LOC I-4c for $C^{(0)}$ (sketched; not done here).
*Last step.* P4 §6, P7 §4: LF-8, not part of I-9; Theorem 3.4 is the cluster input there too (with GAS for the large fields).
*Observable layer (OBS X1–X7).* The second-order components ride on the same constructions: X2 uses Theorem 3.4 only after the stronger two-mark activity condition $\varepsilon_H\le\varepsilon_{\rm PE}/4$ is checked; X3 is the normalization of $\mathscr M^{(k+1)}$ at
$\psi=h$ with the irrelevance of Lemma 3.2 for the one-point terms; X6 is Lemma 5.8 for the second-order data.

---
## 6. Interfaces, findings and errata, Lean plan, open items, questions

### 6.1 Interfaces (proposal; small frozen surface)

| Item | Statement | Freeze? | Consumers |
|---|---|---|---|
| Def-6 / Def-7 (D2) amendment | analyticity of localized terms on $\Xi^c_j(\mathbb B_j(X);1,\varepsilon_j)$ (F-1); sizes $d^{\rm cov}$, mod $\Omega^c$ by Definition 1.1 | with Def-6 | everything |
| I-8 = Theorem 3.1 | the eight expansions | **no** (ruling vi); editable target | I-9, LF-3, LF-5, OBS |
| Lemma 3.2 | termwise I-6 | no (internal) | Prop 3.3, Thm 3.1 (g), Lemma 2.9 |
| Proposition 3.3 | localized interaction | no (internal) | Thm 3.1 |
| Theorem 3.4 | marked cluster expansion on the cubes of $\Omega_{k+1}$ (one and two marks) | no; editable lemma of the polymer layer | Thm 3.1, OBS X2, LF-8 |
| Lemma 4.1, Theorem 4.2 | far data changes; O-2′ | no; editable lemma | LF-3 (LFR Lemma IV.1.3), LF-5 |
| I-9 = Theorems 5.1, 5.2 | whole-lattice step and recursion | editable (the $Z_k=\varnothing$ case of 5.4) | SF milestone |
| Theorem 5.3 | family (F1)/(CONT) clause | **no**, until family and working-neighbourhood inputs are accepted | Root-C via `C1StarF1` |
| Theorem 5.4 | subdomain step (P6 (2.32)–(2.33)) | **no**, until VMOD.md and RGFREE.md inputs close | LF-3, LF-5 |

**[v2: FL-A09, FL-A13]** Theorem 5.3 now quantifies over a common $\nu$-family satisfying `ContAtZero` and the displayed working-neighbourhood condition. Pointwise membership alone cannot imply a family limit. Theorem 5.4 uses the amended Def-7 class and remains conditional on its named OPEN inputs. I-8 is an editable target; it is not currently a proved theorem available to close I-9.

### 6.2 Findings and errata candidates (new rows for `ERRATA.md`, keyed FL-…)

**[v2: FL-A01–FL-A13] Audit errata ledger.** These rows amend the earlier FL-1–FL-13 candidates below; they are not claims that the corresponding external notes are complete.

| Finding | Correction here | Status |
|---|---|---|
| FU-01 [v2.1] | Lemma 2.5: check $\chi_k$'s field, derivative and mass tests and $\chi_{(2.2)}$ against their own thresholds; retain P4 (2.40) ratio | arithmetic REPAIRED; BG/GR domain inputs as stated |
| FL-A01 | §3.2, §3.3: termwise support $X\cup\operatorname{st}_+(y)$, rate cost (3.0), slit-plane domain and actual I-5 support | termwise abstract proof PROVED; RG instantiation/cover OPEN |
| FL-A02 | §2.7, §3.3: modular I-5 and auxiliary margins | DELEGATED to notes/phase1/VMOD.md (in preparation); OPEN |
| FL-A03 | [v2.1] Thm 3.1(f), §3.6, §5.4: P6 Props 2.1–2.2 restriction algebra and conditional complex decay; the $\nu$-free linear mass term belongs to that convention | abstract locality and late absorption proved; actual old-term/H7 and mixed-cover estimates OPEN; see notes/phase1/VMOD.md §2 |
| FL-A04 | §4.2: H7 prefactor $C_F\beta_{k+1}r_{H,k}^2$ and corrected (Λ28′) | complex estimate proved under stated decoupled input; NC/cover OPEN |
| FL-A05 | §4.2: $Y\cap\Omega=\varnothing$ terms enter $b_k$ first | REPAIRED algebraically |
| FL-A06 | §3.4: two marks require $\varepsilon_H\le\varepsilon_{\rm PE}/4$; `hq`, `hκ`, `hα` checked | REPAIRED under landed Mayer hypotheses |
| FL-A07 | Lemma 2.9, §5.2: scalar switch cost separated from joint RG derivative claim | RG part DELEGATED to notes/phase1/RGFREE.md (in preparation); OPEN |
| FL-A08 | §5.2: actual $\varrho_{31}$ and divided free equations | DELEGATED to notes/phase1/RGFREE.md (in preparation); OPEN |
| FL-A09 | Thm 5.3, Lemma 5.8: family premise `ContAtZero` plus working neighbourhoods; preservation proof | conditional on OPEN step/RG inputs; bare `ContAtZero` needs neighbourhood transport |
| FL-A10 | §1.5, Thm 5.1: $\alpha_0,E_0$ fixed before $\beta_*(\alpha_0,E_0)$ | REPAIRED |
| FL-A11 | §1.4: amended $\Xi^c$ input class, exact `i5_background` radii and (DL-gap) | domain arithmetic REPAIRED; fluctuation/modular I-5 OPEN |
| FL-A12 | §1.2, §3.4: finite real penalty $D_\Omega$ on disconnected supports, all-support (G1)–(G3) | REPAIRED subject to connected-cover geometry |
| FL-A13 | summary and theorem status paragraphs: named OPEN premises | REPAIRED as a status correction |

- **FL-1 = F-1** (SF §1.7 ruling (iv)). The data-domain analyticity class cannot be reproduced by the step; use $\Xi^c$ (P4 (H.4)). §1.4. *Design defect in SF, not in the sources.*
- **FL-2 = F-3** (SF §3.7 (R-switch), UNCERTAIN there; P6 p. 11, ER-098, ER-099). With the two-step treatment and the chord identity the switching term is quadratic in
  $\delta\phi=O(\nu)$, i.e. $O(\beta^{-1})$ per block; the scalar action cost is $O(\beta^{-1})$ per block. Its joint $\xi$ derivatives and RG matrix remain OPEN (RGFREE.md); no complete switch claim is made.
- **FL-3** (LFR N-IV-1, Lemma IV.1.8). P5 Prop 3.2's printed $\frac12\beta_k^{-m-1}$ suffices for H4 at $k+1$ because the construction gives $\beta_k^{-m-2}$ (P6 Lemma 4.2). Theorem 3.1 (d). *Resolved.*
- **FL-4 = F-4** (P6 (4.67)). P6 obtains $\eta^{\frac{d-2}2+\gamma-2\alpha_1}$ and claims (H.7)'s $\eta^{\frac{d-2}2+\gamma-\alpha_1}$; the gap closes by using a smaller exponent ($\alpha'=\alpha_1/4$) in the bound
  $p_1(\beta_k)\le C\beta^{\alpha'}\eta^{-\alpha'}$ (P6 uses the same letter $\alpha_1$ for both). *Minor gap, repaired.*
- **FL-5 = F-5** (P4 (2.39); LOC I-4c (ii)). The $\ell^\infty$ bound of $C^{(k)1/2}$ is used but LOC states only $\ell^2$; it follows from the uniform kernel decay (Lemma 2.4 (c)). *Minor.*
- **FL-6 = F-6** (LFR (Λ28), Lemma IV.1.3 route (ii)). P6 (2.13)'s distance $2MR_k$ refers to the margin of $W_{k+1}=(Z^c_{k+1})^{\approx2}$; for the local backgrounds the margin is $E_{Z'}=Z'^{\sim[\hat R_k]}$,
  distance $\approx M[\hat R_k]$; (Λ28) is to be read as the v2 (Λ28′) of §4.2 with prefactor $C_Fa^{-1}\alpha_0^2e^x$, after the empty-intersection split. Its exponential comparison is proved there conditional on the decoupled H7 input.
- **FL-7** (P4 Prop 2.2, p. 696, image). The constant is "const. $\beta^{-\frac58+\alpha_1}\le\frac12\beta^{-\frac14}$"; the P4 review and SF Theorem 4.1 (b) transcribe $\beta^{-(3/8+\alpha_1)}$. *Transcription
  error in the review; no consequence.*
- **FL-8** (P6 (4.1)). The interaction listed in P6 (4.1) omits the $\nu$-free linear term $\nu_k\langle\delta\phi_k,\phi_{k+1}-h\rangle$ of P5 (2.33), which belongs to $V^{(k)}_{\rm eff}$ (P5 (2.38)); it is
  $O(\beta_k^{-1/2}p_1)$ per site, the same order as the cubic term, and is included in (3.3). *Omission in P6, harmless.*
- **FL-9** (P4 (2.27)). At $\lambda=\infty$ the interaction simplifies to $V^{(k)}=\frac12\langle\alpha^{(1)},\phi'\cdot\phi'\rangle+\frac12\langle\phi_2,H_k\phi_2\rangle$ (Lemma 2.3 (b)). *Not an error.*
- **FL-10** (P4 (2.4)–(2.14)). For hard spins the critical point of the Gaussian step is the unique **global** minimiser (Lemma 2.2 (b)); P4 has local uniqueness via P2 Prop 4.1. *Strengthening.*
- **FL-11** (P6 (4.37)–(4.54), p. 44; ER-102). The polymer system modulo $\Omega^c$ is realized on the cubes of $\Omega_{k+1}$ with the size $d_\Omega$ and a pre-summation of labels with equal
  support (Theorem 3.4); no hole parameter is needed in MY, and the landed hole-free `mayer_marked` applies with the finite size of §1.2 and, for two marks, $\varepsilon_H\le\varepsilon_{\rm PE}/4$. *Corrected hypothesis.*
- **FL-12** (P4 (5.31) vs landed `rg_step_infty`). The landed fixed-point bound is $84\eta$ (P4: $2|f(0)|$), so $E_0^*=400C_4'B_6K_0K_5$ instead of P4's $4C_4B_6K_0K_5$. *Constant bookkeeping.*
- **FL-13** (SF §4.4 item 3, P6 (4.54)–(4.56), ER-069, ER-100). Exponent bookkeeping redone: (IC) $\kappa\ge7+8\kappa_0+2c_1$, implied by LFR's $\kappa_{\rm flow}\ge16\kappa_0+16$; P6's own Prop 3.3
  needs $\kappa\ge10+16\kappa_0$, also implied. *Consistent.*

Existing rows touched: ER-059 (I-8 remains conditional on the named OPEN inputs), ER-060 (P6 (4.11) re-proved for $d^{\rm cov}$, Lemma 1.2 (G1)), ER-069 (κ iteration: (IC)), ER-095
(variant (V0)), ER-096 (P6 Props 2.1–2.4: 2.3 proved, 2.1–2.2 sketched, 2.4 = Theorem 5.4), ER-098, ER-099 (FL-2), ER-100 (σ-analyticity, Theorem 3.1 (b)), ER-101 (settled:
$\chi_{\rm fl}$ is a product by definition), ER-102 (FL-11), ER-103 (both values of $\varepsilon$ in P6 Lemma 4.2 are admissible; we use $\beta_k^{-m-2}$).

### 6.3 What changes at $\lambda=\infty$ in the step (collected)

(1) The multiplier replaces $\frac\lambda2(|\phi|^2-1)$; all $\frac1\lambda$-terms of P4 (2.16)–(2.27), (4.2)–(4.14) vanish, and the renormalization constant $d$ does not occur. (2) The quadratic
form is the constrained $\Delta^{(k)}=a_k-a_k^2Q_k(G_k-\Pi_k)Q_k^*$ (`constrainedOp`), positive for real data with the lower bound of GR G-1 (b), (d). (3) The chord identity makes the
expansion around the critical point exact (Lemma 2.3) and the counterterm $C_2$ an exact quadratic form (Lemma 3.5). (4) The critical point is global (FL-10). (5) The switch at
$k_0$ is a quadratic term (FL-2). (6) The fluctuation measure is a product of truncated Gaussians on $\mathbb R^N$ (2.5). (7) At $k=0$ the sphere chart replaces P4 (2.42)–(2.50)
(LFR §II.7, §5.5 here).

### 6.4 Lean plan [v2: FL-A01, FL-A04, FL-A06, FL-A09–FL-A12]

The rows are proposed integration work, not current proof status. The abstract termwise I-6 is already landed in `Balaban/SmallField/RenormTermwise*.lean`. No new module should reprove it; the task is to instantiate its premises for the actual local terms. The background-only `i5_background` is landed, while the fluctuation and modular variants remain separate OPEN gates. Proposed sizes below are retained only as rough planning estimates.

| # | Module | Content | Needs | Lines |
|---|---|---|---|---|
| 1 | `SizeMod.lean` | Definition 1.1 with finite $D_\Omega$ on disconnected supports; prove all-support G1–G3 and connected G4–G5 | `TreeLengthCov`, `PolymerCount`, `Hole` | 1.5k–2.5k |
| 2 | `CriticalPoint.lean` | Lemma 2.2 (Gaussian composition; global minimiser; (2.2)) | Def-5 (`bgField`, BG Thm 5.2 (4)), `theorem73_*` | 0.8k–1.5k |
| 3 | `Expansion.lean` | Lemma 2.3 (chord identity, (2.4), $\nu$-free variant, bounds) | `prop51_*`, `linearResponse`, `constrainedOp` | 1.5k–2.5k |
| 4 | `Covariance.lean` | Lemma 2.4 ($C^{(k)}$, square root by the resolvent integral, $\ell^\infty$ bound, $\log\det$) | GR G-1, G-4 (landed parts), LOC I-4c at $s=1$ | 2k–4k |
| 5 | `Measure.lean` | Lemma 2.5, (2.5), change of variables (2.7), Proposition 2.6 (interpolation identities) | Mathlib `Measure.pi`, linear change of variables | 3k–5k |
| 6 | `Irrelevant.lean` | instantiate `PremisesTerm`/`SumConds`, star support, (3.0), and I-5 evaluation locus for the actual RG terms | landed `RenormTermwise*.lean` | 1k–3k |
| 7 | `I5Variants.lean` | (V0), fluctuation I-5, (Vmod), Lemma 2.8; include (DL-gap) with $C_0=8d+12$ and $C_{\Xi1}=(4d+8)(2d+1)$ | landed background-only `i5_background`; OPEN NC/cover and VMOD.md | 2.5k–5.5k |
| 8 | `Interaction.lean` | Proposition 3.3 | I-4a/b/c (decoupled), AE, 6, 7 | 5k–9k |
| 9 | `Polymer/MarkedCubes.lean` | Theorem 3.4 with finite size, all-support G1–G3 and two-mark $\varepsilon_H\le\varepsilon_{\rm PE}/4$ | `mayer_marked`, `norm_D1_Ff_le`, 1 | 1.5k–3k |
| 10 | `Contributions.lean` | Theorem 3.1 (a)–(e) | 8, 9 | 3k–6k |
| 11 | `Renorm.lean` | Lemma 3.5, Theorem 3.1 (g), (h) | 3, 6, 7, I-4a | 4k–7k |
| 12 | `OldTerms.lean` | [v2.1] Theorem 3.1(f): instantiate actual old-term `PremisesTerm`/`SumConds`, P5 (1.8) restriction, star-crossing allocation, complex H7 source and $\nu$-free $\nu h$ bound; then prove (3.12)–(3.14) and modular resummations | 6, 7, 13; VMOD §2 | 3k–5k |
| 13 | `FarDecay.lean`, `BackgroundChange.lean` | Lemma 4.1, complex H7 prefactor, empty-intersection split, new (Λ28′) | weighted LOC/NC, `isWeight_of_dist`, `theorem73_*`, AE, GM | 3k–5k |
| 14 | `Switch.lean` | scalar Lemma 2.9 plus joint $\xi$ derivatives and scale-sensitive `hηbd` (RGFREE.md) | 3, 6, 13 | 1.5k–2.5k |
| 15 | `SmallField/Step.lean` | Theorems 5.1, 5.2 with $\alpha_0,E_0\prec\beta_*$ and actual $\varrho_{31}$ (RGFREE.md) | 2–14, `rg_step_infty`, `matrixSel`, `norm_xi_le_of_step` | 5k–9k |
| 16 | `SmallField/StepCont.lean` | Lemma 5.8, family Theorem 5.3; prove working-neighbourhood transport to the exact `ContAtZero` output | 15, draft Def-6 `ContAtZero`, `tendsto_rg_solution`, dominated convergence | 2k–4k |
| 17 | `SmallField/StepSub.lean` | Theorem 5.4 | 15, LF Parts I–II declarations | 6k–12k |
| | **Total** | | | **47k–88k** |

**Gates before closure [v2.1].** Module 1 must use a real-valued size on *all* nonempty supports; module 5 must check Lemma 2.5's three separate margins; module 6 must establish actual `PremisesTerm` and the star enlargement; module 9 must verify `hq`, `hκ`, `hα` with two-mark slack; module 12 must address the $\nu$-free H7 mass-domain obstruction; module 13 must use the complex H7 prefactor. Modules 7, 12 and the $\nu$-free part of 14–16 remain OPEN until VMOD.md and RGFREE.md are available. The rough total above is not revised by subtracting already landed termwise files. The first independent milestone is modules 1, 6 and 9; a whole-lattice step still waits for the cover/NC and divided RG gates.

### 6.5 Open items and questions [v2: FL-A01–FL-A13]

1. **VMOD.md, OPEN [v2.1]:** auxiliary-cover margins and NC at the new interface, including the landed `ChainNum.close` condition and either the sufficient $r_0^{\rm Lean}>4dL^3$ margin or another proof of its required smallness; full fluctuation I-5 and (Vmod). For P6 Props 2.1–2.2, §3.6 additionally isolates the actual old-term `PremisesTerm`/`SumConds`, the P5 (1.8) star-crossing restriction, mixed H7 source/response and modular resummations. In the $\nu$-free convention the unrestricted complex H7 conditions alone do not bound $\nu h$ in the linear term of P6 (2.14); specify a bounded complex external-field neighbourhood or another uniform $\nu h$ estimate. VMOD §2.1 assigns that linear term to the wrong convention. These inputs block Proposition 3.3, Theorem 3.1(c),(f), Theorems 5.1–5.4 and the complete O-2′ application.
2. **RGFREE.md (in preparation), OPEN:** the actual $\nu$-free divided equations, $\varrho_{31}$, their analytic/scale bounds, and the joint $\xi$ derivatives of the switch. The scalar identity of Lemma 2.9(a)–(b) is independent of this work.
3. **Actual I-6 premises, OPEN [v2.1]:** instantiate landed `PremisesTerm` and `SumConds` for the scale-$j$ RG terms, including the explicit `Tube`-to-`XiDom`/H7 inclusion, the finite-torus to infinite-polymer transfer of the second-moment cancellation, the P5 (1.8) restriction, and the support enlargement (3.0). The abstract termwise theorem itself is PROVED in Lean; §3.6 identifies the additional star-crossing check for old $j=k$ terms.
4. **Family neighbourhoods, OPEN for the bare class:** either show that `ContAtZero`'s nonempty common open sets transport by analytic continuation to the fixed RG Cauchy polydiscs, or retain the additional working-neighbourhood premise in Theorem 5.3. Verify the physical base family of LFR Theorem II.7.10(e) in the amended class.
5. **Other cited inputs and downstream text:** the $k=0$ covariance analogue of LOC I-4c (§5.5); P1 (3.77), (3.80) for the restored counterterm; P5 §2 bookkeeping and the H7-to-data-domain inclusion with $C_{\Xi1}=(4d+8)(2d+1)$. LFR Lemma IV.1.3 still prints the older $p_0(\beta_k)^2$ complex prefactor and must be updated separately to Theorem 4.2's $\beta_{k+1}r_{H,k}^2$. These are not discharged by the v2 local repairs.

The F-1 class-domain amendment is recorded as accepted in LFR §II.3.3 and in the landed draft Def-6; its subdomain implementation remains an input. The (IC) choice is retained without a PE-L sharpening. No frozen I-8/I-9 claim is proposed while the OPEN items above remain.

### 6.6 Drafting log

Written in one pass, section by section (§1 → §6, then §0). Not done: P6 pp. 15–21 (§3, large-field operators) were not re-read (not needed here); P1 was not re-read (its
statements are taken from SF and the P1 review); P4 §5 beyond pp. 712, 718 was not re-read (SF read pp. 708–718); no numerical constant was optimized.
