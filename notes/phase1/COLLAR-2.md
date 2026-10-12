# The Dirichlet data of the P7 window background

## 1. Decision and scope

Let $G=\mathbb B_{k_1,k}$, $G'=\mathbb B_k(U_k)$, $I_G=\Omega_1(G)$, and $C_G=C(I_G)$. The first background in P7 (2.15)–(2.16) is the background of the **original window spin field** $\widetilde\psi=Q^*(G,\mathbb B_k)\psi$; the second, introduced only in (2.40), is the background of the field composed from $(G',\widetilde\psi_k^0)$. There is no source identity making their Dirichlet data common on $C_G$. In particular, the composition identity in (2.14) concerns a *local step background composed from the window background*; it does not compose the original window field from $G'$.

The P2 convention gives a more precise description than “raw fine field on the whole collar.” The natural lift of a multiscale field at $x\in C_G$ reads the **parent field available at $x$**: a parent block spin $\psi_p(b_p(x))$ if $x$ is in a layer-$p$ part of the parent generating set, and the surviving fine spin $\psi_0(x)$ if $x$ is in its layer-0 part. P5 (1.4) is a decisive special case: $Q^*(\mathbb T^{(k)}_1,\mathbb B_k(W_k))\psi_k$ has the single-scale value $\psi_k(b_k(x))$ on the collar, as well as inside $\Omega_1$; it cannot generally equal $\psi_0(x)$. P2 (4.9), checked on the PDF image of printed p. 633, uses the identity on common blocks, including the layer-0 set, and the block lift on finer blocks. Thus the landed `psiTilde` choice $\psi_0$ at **every** collar point is a convention requiring a boundary-data bridge, not the definition of $Q^*(G,\mathbb B_k)\psi$ established by P7. On the part of $C_G$ where the parent field has layer 0 it is the expected value. On parts where the window gluing in (2.13) uses a different parent piece, the inherited datum must be read from that original piece; the printed formulas do not give a single global parent-layer formula.

**Status.** The source-level distinction and the reference collar formula below are proved. Identification of the physical datum on every collar site of the *glued* window with a concrete parent lift is **OPEN (CB-1)**. A common-data identity is **not proved**, and the printed P7 restrictions do not give a collar estimate of the size needed in (2.49). Therefore P7 (2.49), when inferred solely from (2.47)–(2.48), is **conditional on OPEN (CB-2)** below. This is a statement about the proof's inputs, not a claim that a fully specified P7 history violates (2.49).

## 2. Trace of the two data sets

P7 p. 499 (2.6) writes the original step actions with their original $\psi$ and the local backgrounds $\phi_{j+1}(\mathbb B_{j+1}(\partial\Omega_{j+1});\widetilde\psi)$. Formula (2.7) moves their characteristic functions and exponentials through the Gaussian composition. P7 p. 500 explicitly says that (2.10)–(2.12) renormalize action coefficients **without renormalizing the spin variables**. The window set (2.13) is a gluing of $\mathbb B_{k_1}(W_{k_1})$ in $Z_{k_1}$, $\mathbb B_k$ in $Z_{k_1}^c\cap Z_k$, and $\mathbb B_k(U_k)$ in $Z_k^c\cap\widetilde U_k$. P7 pp. 500–501 then defines $\phi_{k_1,k}=\phi_k(G;\widetilde\psi)$. In (2.14) it composes **this** field into each smaller $\mathbb B_{j+1}(\partial\Omega_{j+1})$ and pays a response remainder; (2.15)–(2.16) place $\phi_{k_1,k}$ in the converted action. Neither factorization nor coefficient conversion substitutes $\phi_k(G';\widetilde\psi_k^0)$ into the first argument's boundary values. LF-RECONSTRUCTION §§III.1–III.2 and P631.md §3, condition (W), describe the same action conversion; (W) is a local-to-window replacement, not a window-to-reference collar equality.

Only later, P7 p. 508 (2.40), defines
$$D'^{\,0}=\operatorname{lift}_k\widetilde\psi_k^0,\qquad
\phi_k^0=\phi_k(G';D'^{\,0}),\qquad
\Psi^0=\psi(G,G';D'^{\,0}).\tag{2.40-c}$$
P2 p. 636 (4.19)–(4.21), checked against the PDF image, sets $a_0^{-1}=0$ and identifies the composed datum on the smaller set's layer-0 gap with the larger field $\phi_k^0$. In the landed language, `composeField_of_collar` proves, for every $x\in C_G$,
$$\Psi^0(x)=\bar\phi_k^0(x)=
\begin{cases}
\phi_k^0(x),&x\in\Omega_1(G'),\\
D'^{\,0}.\Psi(x)=\widetilde\psi_k^0(b_k(x)),&x\notin\Omega_1(G').
\end{cases}\tag{1}$$
The second branch is legitimate because $G\prec G'$ implies that a collar point of $G$ outside $\Omega_1(G')$ belongs to the collar of $G'$. `theorem73_real` and `theorem73_complex` then identify the background of **the composed datum** with $\phi_k^0|_{I_G}$, under their explicit domain and weight hypotheses. These theorems neither identify $D^{\rm ph}.\Psi$ with $\Psi^0$ on $C_G$ nor change the original action. `WindowPieces.windowGenSet_Ω` proves the three-piece layer formula, but supplies no field or collar-data identity, and `WindowPieces.Hyp` is a gluing hypothesis rather than the P7 geometric verification.

P7 pp. 508–509 (2.46)–(2.48) compare $\widetilde\psi$ and $\Psi^0$ only on **window blocks**. The proof of (2.48) writes $\widetilde\psi(x)=\psi_j(y)$ for $x$ in one of those blocks. It has no step for $x\in C_G$. LF-RECONSTRUCTION Lemmas III.4.6–III.4.7 reproduce this interior argument. P7 (2.43) concerns the composed field and a $k$-block field; P5 (1.24) at a fine bond yields an $O(\delta_0)$ comparison. Neither is the missing $O(\widehat W_k\delta_{k_1})$ collar comparison.

## 3. What fails without a collar premise

The omission has a direct variational effect. In the P2 background action the bond term uses $\bar\phi=\phi$ on $I_G$ and $\bar\phi=\Psi$ on $C_G$. Let $e,v\in\mathbb R^N$ be orthogonal unit vectors, set all window block values, reference values and $h$ equal to $e$, and take a collar site $x$ adjacent to an interior site $y$. Set the physical collar spin at $x$ to $\cos\theta\,e+\sin\theta\,v$ and leave the other collar values at $e$. Then $\Delta\Psi$ is zero on every window block, so the interior inequalities (2.47)–(2.48) hold with zero right side; on the collar $|\Delta\Psi(x)|=2|\sin(\theta/2)|$.

This is not merely a bookkeeping difference. At $\theta=0$ the constant background is $e$. Differentiate the constrained Euler–Lagrange equation in the tangent $v$ direction. The first variation $u$ satisfies
$$H u=\mathbf1_y v,\qquad H=-\Delta^D_{I_G}+Q^*aQ+\nu$$
on the tangent subspace (the multiplier's first variation is zero there). Hence $u(y)=\langle\mathbf1_y,H^{-1}\mathbf1_y\rangle v\ne0$. Positivity and Cauchy–Schwarz give
$$\langle\mathbf1_y,H^{-1}\mathbf1_y\rangle\ge
\frac1{\langle\mathbf1_y,H\mathbf1_y\rangle}
\ge\frac1{4d+2+\nu},\tag{2}$$
using $a_nL^{-2n}\le2$ for admissible P2 weights. Analyticity of the small background therefore gives $|\phi_\theta(y)-e|\ge |\theta|/[2(4d+2+\nu)]$ for sufficiently small $|\theta|$. The block interior difference remains zero. Taking $|\theta|=c\min(\delta_0,\delta_1)$ with fixed small $c$ meets either a layer-0 or a layer-1 interface restriction. The P5 running thresholds decay exponentially in $k_1$ while $\widehat W_k$ has the polynomial bound in LF-RECONSTRUCTION (2.26′), so this size is not bounded by a fixed multiple of $\widehat W_k\delta_{k_1}$ in a growing-$k_1$ regime. No constant independent of $k_1$ can turn the interior bound alone into the asserted response scale.

This is a counterexample to the **inference** from the stated interior hypotheses to a background response bound. It is not asserted to be an admissible full history of P7's particular glued geometry. To make it one, one would have to exhibit a relevant $x\in C_G$ whose inherited parent field is an independently variable layer-0 spin and a response point $y$ on the support specified in (2.49). That geometric/field realization is **OPEN (CB-3)**. Conversely, excluding it requires a proved collar identity or a proved estimate. The PDF formulas do not perform either task.

## 4. Correct replacement for P7 Lemma 2.4

Let $D^{\rm ph}$ be the actual inherited P7 datum on $I_G\cup C_G$ (CB-1), $D^0=\operatorname{composeData}(G,G',\phi_k^0,D'^{\,0})$, and define the **full** change
$$\Delta\Psi(x)=D^{\rm ph}.\Psi(x)-D^0.\Psi(x),\qquad x\in I_G\cup C_G.\tag{3}$$
On $I_G$ use P7 (2.47)–(2.48). On $C_G$ a sufficient additional assertion is
$$\sup_{x\in C_G}|D^{\rm ph}.\Psi(x)-\bar\phi_k^0(x)|
\le C_\partial\widehat W_k\delta_{k_1}.\tag{C}$$
It must hold on the collar of every component whose background contributes to the action window. If one proves it only on a thickening of $X_{\rm win}$, one must also give a weighted bound for the omitted collar sites and their distance to each response point; the unweighted supremum on the thickening alone does not control a global background. **OPEN (CB-2)** is precisely (C), together with the domain, smallness and weighted-source conditions used for P3 Proposition 2.1 or its landed response analogue. A stronger alternative, **OPEN (CB-0)**, is an original-action identity $D^{\rm ph}.\Psi|_{C_G}=\bar\phi_k^0|_{C_G}$; this would set $C_\partial=0$. It cannot be imposed by changing `psiTildeData` alone: the boundary bonds of the original action would change.

If (C) is proved, set $C_*=\max(C_{23},C_\partial)$ and $\tau(n)=C_*\widehat W_k\delta_{\max(k_1,\min(n,k))}$. The collar clause of `DataChangeBound` then reads $\tau(1)=C_*\widehat W_k\delta_{k_1}$, exactly. The interior clause follows from (2.48); the adjacent-profile ratio and smallness must be rechecked for $C_*$, not merely $C_{23}$. Under the other hypotheses of `deltaPhi_le_of_dataChange`, its landed conclusion is `LayerBounds` with coefficient
$$K_w C_F e^\epsilon L^{(d-2)/2}\,C_*\widehat W_k\delta_j.
$$
Thus its source-style coefficient in front of $L^{(d+2)/2}\widehat W_k\delta_j$ is $K_w C_F e^\epsilon C_*/L^2$. P7's printed $C_{24}=2K_3C_{23}$ is not retained unless a separate comparison proves that this enlarged coefficient is at most $2K_3C_{23}$. The landed `deltaPhi_le_of_dataChange` gives layered bounds but does **not** by itself prove the exponential factor in P7 (2.49); that factor requires the weighted source localization from P3 Proposition 2.1 at the actual collar and the agreement region. The current LF-RECONSTRUCTION III.4.7 assertion is therefore conditional on CB-1, CB-2 and that weighted localization, or on CB-0 and the weighted localization.

## 5. Corrected Lean interface (proposed; no Lean files changed)

Keep the proved interior reading `psiTilde_of_mem`. Supply a collar datum explicitly rather than assigning layer 0 by default:

```lean
-- ψboundary is the inherited datum of the original action, to be proved
-- from P7 (2.6)–(2.16) for the glued window.
def psiTilde (G) (ψ) (ψboundary : Torus → Fin N → ℂ) (x) (i) : ℂ :=
  if x ∈ G.Ω 1 then (ψ (blockOf ... (G.layerIndex x) x) i : ℂ)
  else if x ∈ collar G then ψboundary x i else 0

def psiTildeData (G) (ψ) (ψboundary) (h) : BgData G N :=
  BgData.clip G (psiTilde G ψ ψboundary) h
    (psiTilde_layerConst G ψ ψboundary) (by ...)

def deltaPsi (Dphysical Dreference : BgData G N) (x) (i) : ℂ :=
  if x ∈ dataSites G then Dphysical.Ψ x i - Dreference.Ψ x i else 0
```

The notation `Torus`, `blockOf` and ellipses here stand for the existing full parameter types and the routine `BgData.clip` proof; this is an interface specification, not a claim that this exact snippet elaborates. Alternatively, define `psiTilde` only on $I_G$ and make `psiTildeData` take `ψboundary` directly. In either design `deltaPsi` is the difference of the **two data objects**, including the collar; zero outside `dataSites G` is harmless. The existing `psiZeroWin` and `windowData` may be retained, since their collar value is correctly given by (1). The current `deltaPsi` in `DeltaPsiDef.lean` is zero off $I_G$ while `psiTildeData-windowData` need not be; hence it must not be used as a full perturbation field.

Required lemmas, in proof order:

1. `window_parent_collar_partition`: for every $x\in C_G$, identify the original piece of (2.13) supplying the boundary spin, including overlap consistency. This is CB-1 and is not in `WindowGenGlue.lean`.
2. `psiTilde_collar_eq_inherited`: the $Q^*(G,\mathbb B_k)\psi$ datum of the action (2.16) equals `ψboundary` on $C_G$. This is the original-action bridge; it must refer to the actual $Q^*$ construction, not `rfl` from a new definition.
3. `psiZeroWin_collar`: for $x\in C_G$, rewrite `psiZeroWin` as `barField G' ... x` by the landed `composeField_of_collar`; split by $x\in\Omega_1(G')$ to obtain (1).
4. `deltaPsi_dataSites`, `deltaPsi_interior`, `deltaPsi_collar`, and `deltaPsi_outside`: prove (3) pointwise and recover the landed interior P7 Lemma 2.3 statement without changing it.
5. Either `original_action_common_collar` (CB-0) with proof from the original expression, **or** `window_collar_bound` (CB-2) on the relevant support with explicit $C_\partial$, complex-domain version, and a weighted-source localization lemma. P5 (1.24) alone is insufficient.
6. `dataChangeBound_of_window_bounds`: combine the interior (2.48) with item 5, use $C_*$ and verify the profile and smallness hypotheses of `deltaPhi_le_of_dataChange`; then a separate `window_response_decay` establishes the distance factor in (2.49).

No theorem in `Composition.lean`, `Theorem73.lean`, or `WindowGenGlue.lean` proves items 1, 2 or 5. The landed `DataChangeBound` collar clause is an **assumption** of `deltaPhi_le_of_dataChange`; it is not a corollary of the proved interior Lemma 2.3.

## Source register

P7: T. Balaban, *The large field renormalization operation for classical N-vector models*, printed pp. 499–501 (2.6)–(2.16), pp. 508–509 (2.40), (2.46)–(2.49), source PDF `sources/s002200050486.pdf`. P2: T. Balaban, *The variational problems for classical N-vector models*, printed pp. 633 and 636 (4.9), (4.19)–(4.21), source PDF `sources/BF02099510.pdf`; formulas checked against the PDF images because `P2-ocr.txt` is unreliable. P5: *Low temperature expansion for classical N-vector models*, printed p. 488 (1.4), text layer `P5.txt`. P3: *Localization expansions. I*, Proposition 2.1, printed pp. 56–57. Local notes: `notes/phase1/LF-RECONSTRUCTION.md` §§II.2.1, III.1–III.2, III.4.4; `notes/phase1/P631.md` §3; `notes/phase1/COLLAR-RULING.md`. Landed Lean declarations checked in `Balaban/Background/Composition.lean`, `Theorem73.lean`, `Balaban/LargeField/R/WindowGenGlue.lean`, `DeltaPsiDef.lean`, and `DeltaPhi.lean`. All source and Lean paths in `/home/scott/Balaban` were read only.
