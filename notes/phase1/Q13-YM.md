# Q13-YM: the Yang-Mills free-source design against Blocker 2

Design note, no Lean edits. YM reading: https://github.com/ethanwsussman/Yang--Mills-LLM-experiment (commit e392ef4, part I,
cited I:line). The account is unrefereed; YM statements are SOURCE (as printed there). Landed facts: `Q13-DECISION.md`,
`Q13-LATE.md`, `Q13-LATE2.md`, `Q13-HYBRID.md`.
## Verdict
(1) A0 puts the complete background in the sharp indicators, so they depend on h (S5(i) fails). YM avoids the analogue because
its supports contain no source; the O(N) design with that property is A0' (massless cutoffs for j <= k_0), not A0. (2) No switch
removes the switch cost but not c beta q^2 as a bound on the weight over the complex domain; YM ties its current radius to the
coupling; the O(N) radius that does the same is beta_k^{-1/2}, which the class does not carry. OPEN. (3) The collar tests can
be extended (changes chiK, chiY, ChiDomProp); the reserve pays a power of the log. (4) Route R-YM in section 5; addendum in section 6.
## 1. A0, S5(i), and the YM mechanism
**PROVED (`Q13-DECISION.md` s.4).** A0 uses mu_j = nu_j L^{-2j} > 0 in every SF term, LF set, cutoff, action and R reference, so
SF and LF factors agree pointwise. The explicit conjunct |phi-h| < delta_j/sqrt(nu_j) is redundant for real unit phi, h when
beta_j nu_j <= E and A_0^2 lambda_*^{2p_0} > (64/9) a E. BlockClose, GradClose and the domain read phi^{m,h}(Psi), so depend on h.
**PROVED (same).** S5(i) (LF-RECONSTRUCTION II.5.7) asks the Borel set of a core kernel invariant under Psi -> R Psi with h fixed;
III.9.4-III.9.5 rotate the real contour on that equality. Joint covariance gives only P(R Psi, R h) = P(Psi, h). Separately,
P7 Lemma 2.1 fails at zero tolerance for every m > 0 (one-spin example (4.1) there).
**SOURCE (I:156838-157010, Prop. 4.32 (d1)-(d2); "proof outstanding").** The support S_omega of all characteristic functions of
a history is Borel, determined by (X, omega, k, g_0..g_k, p), independent of the background pair (U,J), of V_k outside X, of K
and of the torus. The (U,J)-dependence is only in e^{Phi_omega}, finite on S_omega x D_k(X), real on real pairs. Mechanism: YM
tests are gauge-invariant functions of the integration variable; YM has no external field, and the free current J (I:45237-45330,
form Q at free J) is a multiplier entering only the exponent. So the YM design does avoid the analogue of S5(i), by construction.
**REFUTED (literal transfer).** O(N) with nu > 0 has a preferred direction and P5 (1.19) tests |phi_square - h| for k > k_0.
What transfers is the split: sets free of the source below k_0, source in the weight. That is A0' (`Q13-HYBRID.md`): massless
cutoffs and R reference for j <= k_0 (S5(i) holds verbatim), complete background in the physical action and inherited SF terms.
For k > k_0, R is the identity (P7 Theorem 2, p. 497), S5(i) is not used, and h may enter the tests. YM thus supports A0' over A0
on S5(i). It does not close the A0' items: real overlap margin of a sharp cutoff, the physical factorization, the R window estimate.
## 2. The source as a free complex variable (question 2)
**PROVED (one block, item 13).** With b = nu h, q = |b_perp|: complete minus free action is beta(R-(a+m)) = beta q^2/(R+a+m) >=
c beta q^2, R = sqrt((a+m)^2+q^2). Since nu_k <= (7/8)L^{-2} in scale-k units (P4), a+m is of order 1 at every scale, so an
O(1) factor per block needs |b_perp| <= c beta_k^{-1/2}, independent of the mass.
**PROVED (conditional on A0').** With massless indicators and b free there is no comparison of two backgrounds: beta A^{m,b} -
beta A^0 is a weight on a common support. On real unit h it lies in [-2E n_j(C), 0] ((5.1) of `Q13-DECISION.md`). On complex b it is
analytic for |q| < a+m, with modulus bounded iff beta_k |q|^2 <= C. So the free-source reading holds exactly on |b_perp| <= c beta_k^{-1/2}.
**SOURCE (I:135160-135180, I:142592-142700).** YM radii are tied to the coupling: alpha_{0,0} = C e^{-t_0/2} t_0^q and
epsilon_0 = A_0 e^{-t_0/2} t_0^{p_0}, with e^{-t/2} the coupling, so beta r^2 is a power of t. The current radius
gamma_0^(k) = 5 max_{j<=k} w_*(j) alpha_bar_j is non-decreasing in k by the maximum. Older terms then live on a smaller radius
than their consumers read, and a larger radius is not contained in the old space: open at case (4b), I:135200-135235 and I:135430
(a raw point held by no live piece across an increase of density; step (*) unproved), and shown sharp by the one-point probe
P_y(c) (I:135723-135800): P_y(c) is in the radius-gamma space iff l^3 c <= gamma.
**OPEN (the O(N) role of gamma_0^(k)).** It is the transverse radius r_k of the source polydisc. Candidates: P1 (3.13),
r_k = epsilon sqrt(nu_k), growing by L per step (nu_{k+1} = nu_k L^2 (1+xi_3)/(1+xi_2)), with exponent epsilon^2 beta_k nu_k, which is
O(1) only for k <= k_0 + O(1); or r_k = c beta_k^{-1/2}, shrinking in level-0 units, so an old term is restricted, not extended,
and the YM case (4b) does not arise in this direction. The class (P3 (4.26)) carries epsilon_j independent of the mass, with
epsilon_j^2 above nu_{k+1} e^{-2 epsilon}/beta (polylog excess over beta_j^{-1/2}); the exponent beta epsilon_j^2 is then a power
of the log, not O(1), and RGFREE-6 s.3 shows a model where the activity is unbounded. YM gives no estimate here: its radii are
chosen, not derived. OPEN: the Cauchy bound for (I-6) on radius beta^{-1/2} (second b_perp derivative of E costs beta E_0).
## 3. The collar (question 3)
**SOURCE (CMP119 p. 248; I:142592-142700).** Hypothesis (a): for real data in the support of the characteristic functions, every
pinned plaquette within 2LM R_check_1 of Omega_1 has |V_0(dp)-1| < epsilon_0. The step-zero tests reach the whole never-averaged
collar the background reads; the lemma then gives Q_1 = Q_5 < epsilon_0, Q_6 = Q_7 = 0, Q_3 <= 0.48 r_3(0) on the collar. The
background estimate on the collar is printed without proof in YM too (CMP99b (3.35), (3.37); CMP109 pp. 263, 277); YM supplies
the test, not the estimate.
**PROVED (mismatch, `Q13-LATE2.md`).** chiK reads data within square^{~3}, direction is tested within square^~, the data of
G = B_k(W_2(Y)) reach 2 floor(R_{k-1}) + 3 cubes from Y, and ChiDomProp has no h.
**ROUTE (P5 (1.19)-(1.31)).** Replace square^~ in the FieldClose conjunct by the neighbourhood of radius rho_k = 2 floor(R_{k-1}) + 3
cubes, so every datum site of G is tested. Changes: (1.19) the test region and chiK stencil; (1.22) the factorization needs
U~ and U'~ at distance > rho_k; (1.24) gains |psi_i(b) - h| < 2 delta_i/sqrt(nu_i) on layer-i blocks (RD of `Q13-LATE.md`);
(1.27) a large-field component absorbs the cubes within rho_k of a failing cube, so its volume grows by up to (2 rho_k+1)^d, a
power of lambda_{k-1}^2; (1.30)-(1.31) the reserve beta delta^2 = A_0^2 lambda^{2p_0}/a must exceed it, which a larger p_0
gives, as YM's t_0^{p_0} beats its collar count. OPEN: p_0 against P5 (1.30) is unchecked, as is the complementary sector.
## 4. Where YM does not help
SOURCE/OPEN: the account lists the collar-alignment estimate as unproved in YM (ym4 item C13); (d1) is "proof outstanding"; YM
has no mass forcing of size nu_k at k > k_0 (`Q13-LATE.md`, half-space model), so the O(N) retained-shell problem is stronger.
## 5. Recommendation: route R-YM (A0' plus extended direction tests), leaves <= 300 lines each
1. Three masses in `OpConsts` (`mu` action, background, cutoff); changes `LargeField/Operators/Quiet.lean` (lines 153-193),
   `Def6v2Regime.lean` (`lfBgMass`); as in `Q13-HYBRID.md` item 1.
2. `support_h_free_below_k0`: for j <= k_0 the indicators are functions of Psi alone, so S5(i) holds (new file).
3. `weight_common_support`: e^{-beta(A^{m,b}-A^0)} finite and analytic in b_perp for |q| < a+m; bounds e^{2En} (real unit h) and
   e^{beta|q|^2/(2(a+m))} (complex b) (new file).
4. `extended_direction_stencil`: radius rho_k; changes `Characteristic/Reg.lean` (FieldClose), `Characteristic/Stencil.lean`
   (chiK_stencil), `Def7SmallField.lean` (chiY).
5. Direction clause in `ChiDomProp`/`ChiDomAt` for k > k_0; changes `Characteristic/OperatorDomain.lean`, `Operators/StepData.lean`,
   `locOp_vanish_chiDom`, `DomainIdentity` (Q13-LATE2 minimal repair, plus the complementary-sector cost).
6. `LateParentR3` from 4, 5 (packages 2-4 of `Q13-LATE.md`). 7. `collar_reserve`: (2 rho_k+1)^d < beta delta^2 for p_0 > p_*(d).
Not routed (OPEN): the activity bound on radius beta^{-1/2} and the complete-action R window estimate.
## 6. Item 13, fifth addendum (text-ready)
In Balaban's Yang-Mills papers the current is a free complex variable at every scale, the background is never switched, and the
supports of the characteristic functions do not involve it (CMP119 pp. 246-248; CMP109 pp. 263, 277). Is the O(N) reading the
same: for k <= k_0 the sharp sets of P5 (1.18)-(1.19) and the reference of P7 are massless and the source enters only the
weights, which are then analytic in b on a transverse polydisc of radius of order beta_k^{-1/2}? Which transverse radius does
the inductive class carry for k <= k_0 and for k > k_0, and does it shrink or grow with k? In Yang-Mills the tests reach every
pinned plaquette within 2LMR_1 of the large-field region (CMP119 p. 248), so the collar data the background reads are tested;
is P5 (1.19) to be read with square^~ replaced by the neighbourhood of 2R_{k-1}+3 cubes, or does a different argument give the alignment on the retained shell?

W862 status (leaves 2, 3, 7 of section 5; files Balaban/LargeField/Regime/A0Prime{Support,Weight,Reserve}.lean, no landed file changed):
leaf 2: reg/chiK/chiPrimeNew/chiY at mass 0 (and nu_k = 0) are h-free for constant real h; S5(i) follows from chiK_rot (chiK_zero_mass_rot_fixed_h, chiPrimeNew_zero_mass_rot_fixed_h).
leaf 3: weight_real_bounds (landed actionG, e^{-2E|X|} <= w <= 1); complex source: entire, |w| <= e^{beta mu |C| |Im h|^2/2}; one-block R-c analytic on |q|<c with |w| <= e^{beta|q|^2/c}; the constant 1/(2c) is FALSE (blockGap_re_lt_of_imag).
leaf 7: collar_reserve with p_*(d) = d and A0^2 lam_{k-1}^2 > a (4 R_b + 7)^d.
