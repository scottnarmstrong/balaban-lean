# Paste text for LF architecture version 4

This note uses the notation and constants of LF-ARCHITECTURE.md v3, commit `9c37838`. It replaces the window paragraphs of §3.5, Lemma C(e)–(f), the relevant part of §3.8, and the theorem statement in §4. It is an audit of the replacement text as well as proposed text. In particular, a geometric path lemma is proved below, but its use with the precise characteristic functions in a several-component history has an identified outstanding localization obligation. No claim that LF-4 is closed follows from this note.

## B. Pending cores: replacement for §3.5 and §4.5

### B.1 State and deterministic transitions

Write $\mu=k+1$. Use the disjoint state type
$$\mathsf{WindowState}=\mathsf{Pre}\;|\;\mathsf{Pending}(q,\nu)\;|\;\mathsf{Active}(q,\nu,\mathcal M),$$
where $q\in\mathbb N$, $\nu\in\mathbb N_{\ge1}$, and $\mathcal M$ is a finite set of scales. This is the tagged extension of `Option (Nat × Nat × Finset Nat)`; the old `none` is `Pre`, and the old `some` is split according to whether its core has occurred. The admissibility conditions at scale $k$ are
$$\begin{array}{lll}
\mathsf{Pre}:&q:=s>k,\quad \nu:=1,\quad\mathcal M:=\varnothing;\\
\mathsf{Pending}(q,\nu):&k<q\le k+h_k+1,\quad1\le\nu\le\nu_{\max}(k),\quad\mathcal M:=\varnothing;\\
\mathsf{Active}(q,\nu,\mathcal M):&q\le k,\quad1\le\nu\le\nu_{\max}(k),\quad\mathcal M\subset(q,k].
\end{array}\tag{B.1}$$
For each state set $t^*=\max(q+n_q(q),s+n_2(s))$ and $U=\frac12\sum_{\xi\in\mathcal M}\tau_\xi$. Thus `Pre` and `Pending` have $U=0$. A pre-window component has $t^*=s+n_q(s)$ because $n_2\le n_q$. A pending component cannot be ripe: $t^*\ge q+n_q(q)>q>k$. The spine $\Gamma$, gain clock $b$, smallness clock $s$, and genealogy of the seeds remain part of the history as in (U1)–(U4). In addition to (3.1), the inductive geometric certificate is
$$\mathsf{Cover}_k:\quad \text{every Active or Pending component is covered by at most $\nu$ boxes of side $\mathrm{crit}_k$.}\tag{B.2}$$
This certificate applies at the *current* scale even when $q>k$. The history remembers which entries were certified one-box entries; it is not necessary to store a second list of entry dates in `WindowState`.

For any finite set $E$ of merge scales let $B(E)=\bigcup_{\xi\in E}[\xi,\xi+h_\xi]$. Classify the result of every transition *after* the spine update and canonical hull closure. The following list is exhaustive.

1. **Pure shadow, without a contact.** Apply (U1), including a hull which does not touch another component. `Pre` remains `Pre` until the spine is a point. A point spine makes the result `Active(\mu,1,\varnothing)` and records a one-box entry at $\mu$. `Active(q,\nu,\mathcal M)` retains its data. `Pending(q,\nu)` retains its target if $\mu<q$; if $\mu=q$, it becomes `Active(q,\nu,\varnothing)` by the activation lemma below. A hull of an already Active or Pending component does not discard its old certificate or bank. The clocks are updated by (U1)/(U3), so $s'\le s$ and $t^{*\prime}\le t^*$.

2. **New large-field cube.** If $r\ge1$, with any number $m\ge0$ of old parts and with any mix of their states, apply (U2) and (U3), set $b'=\mu$, and discard all old merge records and banks. A point spine gives `Active(\mu,1,\varnothing)` and a one-box entry; otherwise the result is `Pre`. This includes a new cube alone, a gain into one component, and a gain which joins several components. A hull contact is counted in $m$.

3. **Pure merge with a Pre part.** If $r=0$, $m\ge2$, and at least one part is `Pre`, use precisely the restart in item 2, with $b'=\max_i b_i$ rather than $\mu$. The output is `Pre` or a box-certified `Active(\mu,1,\varnothing)` according as its final spine is non-point or point. Active and Pending records in the other parts are discarded.

4. **Pure merge of window-bearing parts within the cap.** Here every part is Active or Pending and $\nu':=\sum_i\nu_i\le\nu_{\max}(\mu)$. Put $\mathcal M_i=\varnothing$ for Pending parts and define
   $$\widetilde q=\max_iq_i,\qquad E=\bigcup_i\mathcal M_i\cup\{\mu\},\qquad t_0=\max\{\widetilde q+n_q(\widetilde q),s'+n_2(s')\},$$
   $$T=\min\{t\ge t_0:k_1(t)\notin B(E)\},\qquad q'=k_1(T),\qquad\mathcal M'=E\cap(q',\infty).\tag{B.3}$$
   If $q'>\mu$, output `Pending(q',\nu')`; necessarily $\mathcal M'=\varnothing$. If $q'\le\mu$, output `Active(q',\nu',\mathcal M')`. The old histories are joined, and the output has $t^{*\prime}=T$. A merger behind an already Pending target may have $\mu<q'$ and need neither a new deposit nor a change of target.

5. **Pure merge overflowing the cap.** If all parts are Active or Pending and $\sum_i\nu_i>\nu_{\max}(\mu)$, use the restart in item 3. The output has $\nu'=1,U'=0$; a point output is certified at $q'=\mu$.

6. **$R$ at scale $k\le k_0$.** Apply $R$ only to Active components with $t^*=k$. A removed component has no successor and no remaining bank. A kept component has unchanged domain and point spine, $b'=k$, and `Active(k,1,\varnothing)`; its one-box entry is certified by the ripe shape statement. Its former bank is discarded. Non-ripe components, including every Pending component, are unchanged.

7. **End of the window regime.** After $R^{(k_0)}$, discard the state, $t^*$, $\nu$, and $U$ only *after* applying the transfer to (H6-flat) in §4.7. For $k_0<k\le k_f$ use the flat recurrence, with no $R$. A Pending target beyond $k_0$ requires no activation.

The base is $Z_0=\varnothing$. Each component at scale $1$ is an item-2 event with $m=0$, $r\ge1$, charged by (B) at $k=0$. These rules also cover a hull-induced contact: it is an event, never a pure-shadow hull.

### B.2 Closure, bounded horizon, and activation

**Lemma C4 (pending-core closure).** Under (G1)–(G2), (K), and sufficiently large $\lambda_0$, (B.1)–(B.2) hold after every transition. If (B.3) is used at scale $\mu$, then
$$\widetilde q\le\mu+h_\mu,\qquad k_1(s'+n_2(s'))\le\mu-1,\qquad q'\le\mu+h_\mu+1.\tag{B.4}$$
The pending horizon is therefore at most $h_k+1=O(\log\lambda_k)$ scales ahead of the current scale. Moreover $q'\ge\max_iq_i$ and $t^{*\prime}=T$, so a later target never moves backward.

*Proof.* The cover survives a shadow because a box of side $\mathrm{crit}_k$ produces a box of side at most $\mathrm{crit}_k/L+2+2s_*r_k\le\mathrm{crit}_{k+1}$, as in v3 Lemma C(b). A merge takes the union of the covers; a point spine or hull is one box. For a window-bearing merger, (4.1) and the cap give $\ell'\le(\nu'-1)D_\mu\le\nu_{\max}(\mu)D_\mu$. Consequently
$$s'\le\mu+\lceil\log_L\max(\ell',1)\rceil\le\mu+C\log\lambda_\mu,\qquad s'+n_2(s')\le\mu+C'\log\lambda_\mu.$$
On the other hand $\mu+n_q(\mu)>\mu+\lambda_\mu/(\alpha\log L)$. For large $\lambda_\mu$, $s'+n_2(s')<\mu+n_q(\mu)$; hence $k_1(s'+n_2(s'))\le\mu-1$. Each Active input has $q_i\le\mu-1$. Each Pending input has $q_i\le(\mu-1)+h_{\mu-1}+1\le\mu+h_\mu$, proving the first two assertions. Since $k_1$ is nondecreasing,
$$c:=k_1(t_0)=\max\{\widetilde q,k_1(s'+n_2(s'))\}\le\mu+h_\mu.$$
Every record in $E$ has scale at most $\mu$ and $h_\xi\le h_\mu$. Thus $\mu+h_\mu+1$ is outside every strip in $B(E)$, and the first admissible core $q'$ lies between $c$ and $\max(c,\mu+h_\mu+1)=\mu+h_\mu+1$. Pure shadows preserve the horizon since $h$ is nondecreasing. The inverse property of $k_1$ gives $q'\ge\widetilde q$ and $q'+n_q(q')\le T<(q'+1)+n_q(q'+1)$. If $T>t_0$, it is the first time the blocked value of $k_1$ changes to $q'$, so $T=q'+n_q(q')$; if $T=t_0$, the smallness inequality in $t_0$ already holds. Hence $\max(q'+n_q(q'),s'+n_2(s'))=T$. $\square$

**Lemma C(e)–(f), replacement.** For an Active component at scale $k$ with core $q$, trace its ancestors back through Active/Pending merges, stopping each branch at its most recent certified one-box entry (a W1 entry, a point restart, or a kept $R$). Such entries may themselves be merges at their entry scales; all mergers *before or at* an entry are exempt from the strip assertion. Every merge at a scale $\xi\le q$ **after those entries** satisfies
$$\xi+h_\xi<q.\tag{C-e4}$$
Every merger after the core is in the retained record $\mathcal M\subset(q,k]$. At scale $q$, every component of the lineage is one box of side at most $\mathrm{crit}_q$, and different lineage components are $*$-separated. Also
$$q+n_q(q)\le t^*<(q+1)+n_q(q+1),\qquad k_1(t^*)=q.\tag{C-f4}$$
Thus at ripeness $t^*=k$, the core used by $R$ is exactly $q=k_1(k)$. The literal sentence “there was no lineage merge in $[q-h_q,q]$” must be replaced by (C-e4) with its last-box-entry exception; a point restart at $q$ is an allowed counterexample to the literal sentence.

*Proof.* A point entry is a box by §4.3. Suppose first that one lineage component at scale $q$ has no post-entry merge. Its shadows remain covered by one critical box, and a hull makes it a box. Otherwise let $\xi\le q$ be its last post-entry merge. At the (B.3) transition which made $\xi$ no longer a retained post-core record, the chosen core was outside $[\xi,\xi+h_\xi]$; monotonicity of cores gives $\xi+h_\xi<q$. At scale $\xi$ the merged component is connected and covered by at most $\nu_{\max}(\xi)$ critical boxes, so its diameter in $\pi_\xi$ units is at most $\sqrt d\,\nu_{\max}(\xi)\mathrm{crit}_\xi$ (the weaker bound with an extra fixed factor is harmless). With $n=q-\xi\ge h_\xi+1$, the no-merge shadow recurrence gives
$$e_q\le L^{-n}\sqrt d\,\nu_{\max}(\xi)\mathrm{crit}_\xi
       +\sum_{a=0}^{n-1}L^{-a}(2s_*r_q+2)
\le L^{-h_\xi-1}\sqrt d\,\nu_{\max}(\xi)\mathrm{crit}_\xi
       +\frac{2s_*r_q+2}{1-L^{-1}}<\mathrm{crit}_q.\tag{B.5}$$
The last strict inequality follows from $L^{h_\xi}\ge L^2(2\sqrt d\,\nu_{\max}(\xi)M\mathrm{crit}_\xi)$, $M\ge1$, and $c_0(1-L^{-1})\ge s_*+1$; increasing $\lambda_*$ handles the fixed rounding constants. The canonical hull makes this component one box no later than $q$. Since $\xi$ was its last merge, later hulling creates no contact. At $q$ distinct components are $*$-separated by the component convention. If activation occurs on a pure shadow at $q$, this argument applies verbatim. If an event occurs at $q$, a point restart is a new certified entry, while a (B.3) merger at $q$ cannot activate with core $q$: that value lies in its newly blocked strip. This proves the shape statement and the C-01 exception. Formula (C-f4) holds at entries, by Lemma C4 after a merge, and persists under pure shadows since $s$ and $t^*$ can only decrease while $t^*\ge q+n_q(q)$. $\square$

The full covered-window conclusions should read as follows. For Active $q\le k$, no gain occurs on the steps $q\to q+1,\ldots,k-1\to k$, $b\le q$, the lineage at each $j\in[q,k]$ has a $\nu$-box cover, and $\ell\le(\nu-1)D_k$. For Pending, the current cover (B.2), spine bound, and $b\le q$ hold, but there is no historical domain $Z_q\cap Z$ yet. Only Active ripe components enter the hypotheses (RQ) of §3.8.

**Status of B.1–B.2:** proved under the stated abstract geometry and large-$\lambda_0$ assumptions, with high confidence. The proof gives a finite horizon and checks the event-at-activation case. The claim is an internal mathematical argument, not a Lean proof.

### B.3 Budget calculation replacing §4.5

Keep $\tau_t,v_j,w_j,\sigma_k,E_k$ and (H6′) from §§4.2–4.4, with $U=0$ in Pending. Let $\mu=k+1$, $\lambda=\lambda_\mu$, and put
$$A(t)=2A_2p_2\theta_+\lambda_t^{p_2-1}+C_w\lambda_t^{2d+1},\qquad W_\mu(t)=\sum_{j=\mu}^{t}w_j.\tag{B.6}$$
The sufficient event inequality is exactly (4.2), now for Active *and* Pending inputs:
$$\sum_i\tau_{t_i^*}+\sum_iW_\mu(t_i^*)+rg_k+v_\mu\sum_i\ell_i/L+\sum_i(\nu_i+U_i)
\ge\tau_{t^{*\prime}}+W_\mu(t^{*\prime})+(m+r-1)E_\mu+\nu'+U'.\tag{B.7}$$
Every old $t_i^*>k$, hence $t_i^*\ge\mu$. The estimates below are uniform in the number of parts. Constants denoted $C$ depend only on the typing data, not on $k,m,r$ or the history.

**Quiet shadow, including Pending activation.** The old spine term satisfies $2\sigma_k\ell=(2/L)(v_\mu+\sigma_\mu)\ell$. The loss is at most $v_\mu\ell/L+w_\mu$, while $\ell'\le\ell/L$, $t^{*\prime}\le t^*$ and $\nu',U'=\nu,U$. Therefore
$$G'\ge\tau_{t^*}+2\sigma_\mu\ell/L+\sum_{j=\mu+1}^{t^*}w_j+v_\mu\ell/L+\nu+U
\ge\tau_{t^{*\prime}}+2\sigma_\mu\ell'+\sum_{j=\mu+1}^{t^{*\prime}}w_j+\nu'+U'.$$
At $\mu=q$ the Pending-to-Active change changes no numerical term. The output has $t^{*\prime}\ge\mu$, with equality only if it is a ripe Active component to be processed by $R$.

**A new cube, $r\ge1$.** This is a restart, so $\nu'=1,U'=0$ and all $U_i\ge0$ may be dropped. It suffices to prove
$$m\tau_\mu+rg_k+v_\mu\sum_i\ell_i/L
\ge\tau_{t^{*\prime}}+W_\mu(t^{*\prime})+(m+r-1)E_\mu+1.\tag{B.8}$$
Set $\Lambda'=\log_L\max(\ell',1)$. Lemma T′ gives $t^{*\prime}\le\mu+1+\Lambda'+n_q(\mu+1+\Lambda')$ and $\lambda_{t^{*\prime}}\le C(\lambda+\Lambda'+1)$. If $\Lambda'\le\lambda$, then
$$\tau_{t^{*\prime}}+W_\mu(t^{*\prime})+1\le C_1\lambda^{p_2}+C_2\lambda^{2d+2}+1,$$
and $(m+r-1)E_\mu\le(m+r-1)C_E\lambda^{2d+1}$. For large $\lambda$, $\tau_\mu\ge E_\mu$ and $g_k\ge E_\mu+C_1\lambda^{p_2}+C_2\lambda^{2d+2}+1$, so (B.8) follows (also at the base, $m=0$). If $\Lambda'>\lambda$, (4.1) gives $L^{\Lambda'}\le H+F$, where $H=\sum_i\ell_i/L$ and $F=(m+r-1)D_\mu$. The new threshold plus waiting sum is at most $C\Lambda'^{p_2}$, since $p_2\ge2d+3$. If $H\ge\frac12L^{\Lambda'}$, then $v_\mu H\ge c\lambda L^{\Lambda'}\ge C\Lambda'^{p_2}+1$. If $F\ge\frac12L^{\Lambda'}$, then $m+r-1\ge L^{\Lambda'}/(2D_\mu)\ge C\Lambda'^{p_2}+1$ for $\Lambda'>\lambda$ large; one unit from each old threshold or gain pays this count, and the rest pays $(m+r-1)E_\mu$. Thus (B.8) holds.

**Within-cap pure merge, all parts Active or Pending.** Let $i_0$ maximize $t_i^*$, let $c=k_1(t_0)$ in (B.3), and define
$$\Delta_1=(t_0-t_{i_0}^*)_+,\qquad\Delta_2=T-t_0,\qquad X=\{\xi\in E:\xi<q',\ \xi+h_\xi\ge c\}.\tag{B.9}$$
The distinct old merge records contribute their banks only once to the output; duplicate scales in different input records give extra slack. With $D=[\mu\in\mathcal M']$, direct set subtraction gives
$$U'-\sum_iU_i\le\tfrac12D\tau_\mu-\tfrac12\sum_{\xi\in X,\ \xi<\mu}\tau_\xi,\qquad D\le[\mu\notin X].\tag{B.10}$$
There is no deposit when the new merger lies behind a Pending target and is released immediately. There is no double spending: a bank disappears from $\mathcal M'$ at the one transition which crosses its strip and never reappears, since cores never decrease.

The longest-spine argument of v3 §4.5 applies to Pending parts because of (B.2):
$$\Delta_1\le\bar\Delta:=3+\log_Lm+\log_L(1+D_\mu)+n_2(\mu+1+\Lambda').\tag{B.11}$$
The integer core scales $[c,q'-1]$ are covered by the strips indexed by $X$. If $X=\varnothing$, then $\Delta_2=0$. Otherwise
$$q'-c\le\sum_{\xi\in X}(h_\xi+1),\qquad
\Delta_2\le c_*\sum_{\xi\in X}(h_\xi+1)+1\le\sum_{\xi\in X}\{c_*(h_\mu+1)+1\}.\tag{B.12}$$
Lemma C4 gives $q'\le\mu+h_\mu+1$, while $\widetilde q\le q'$. Consequently, for large $\lambda$,
$$\lambda_{T}\le2c_*^2\lambda_{\widetilde q},\qquad
\xi\in X\Longrightarrow \xi\ge c-h_\mu\ge\widetilde q-h_\mu
\Longrightarrow\lambda_\xi\ge\tfrac12\lambda_{\widetilde q}\ge\frac{\lambda_T}{4c_*^2}.\tag{B.13}$$
For the new $\xi=\mu$, the same comparison holds. Since $h_\mu=O(\log\lambda)$, increasing $\lambda_*$ makes the following explicit per-merge inequality true for every $\xi\in X$:
$$\tfrac12\tau_\xi=A_2\lambda_\xi^{p_2}
\ge \{c_*(h_\mu+1)+1\}A(T).\tag{B.14}$$
The current merge frees at least $(m-1)\tau_\mu$ from the $m-1$ thresholds other than $t^*_{i_0}$. Set aside $\tau_\mu/2$ for its deposit if $D=1$, or for its crossed strip if $\mu\in X$; if neither occurs this half is unused. Every old crossed strip is paid by the corresponding released bank in (B.10) using (B.14). The remaining sufficient inequality is
$$\tfrac12(m-1)\tau_\mu+v_\mu\ell_{\max}/L
\ge \bar\Delta A(T)+(m-1)E_\mu.\tag{B.15}$$
Here the cap and (4.1) improve the v3 proof: $\ell'\le(\nu'-1)D_\mu\le\nu_{\max}(\mu)D_\mu$, so $\Lambda'=O(\log\lambda)$, $m\le\nu_{\max}(\mu)$, $\bar\Delta\le C\log\lambda$, and $\lambda_T\le C\lambda$. Thus
$$\bar\Delta A(T)+(m-1)E_\mu
\le C\log\lambda\,\lambda^{\max(p_2-1,2d+1)}+(m-1)C_E\lambda^{2d+1}
\le\tfrac12(m-1)\tau_\mu,$$
for $m\ge2$, $p_2\ge2d+3$ and large $\lambda$. This proves (B.15), hence (B.7), including repeated Pending pushes and nested strips. No large-$\Lambda'$ branch is possible in this case.

**Pure merge with at least one Pre part.** It restarts, so $\nu'=1,U'=0$. Let $i_0$ maximize $t_i^*$, and use the v3 §4.5 Case 2b bound (valid for Pending inputs by (B.2))
$$\Delta=(t^{*\prime}-t_{i_0}^*)_+\le\bar\Delta'
:=c_*\{2+C_3\log\lambda+\log_L[m(1+D_\mu)]\}+2.\tag{B.16}$$
After cancelling the $i_0$ threshold and its waiting sum in (B.7), dropping all old banks and using $\sum_i\nu_i\ge\nu'=1$, the sufficient inequality is
$$ (m-1)\tau_\mu+v_\mu\ell_{\max}/L
\ge\bar\Delta' A(t^{*\prime})+(m-1)E_\mu.\tag{B.17}$$
If $\Lambda'\le\lambda$, then $\lambda_{t^{*\prime}}\le c'\lambda$ and $\bar\Delta'\le C(\log\lambda+\log m)\le C(m-1)(1+\log\lambda)$, so the right side is at most $(m-1)C(1+\log\lambda)\lambda^{\max(p_2-1,2d+1)}\le\frac12(m-1)\tau_\mu$. If $\Lambda'>\lambda$, (4.1) gives either a spine $\ell_{\max}\ge L^{\Lambda'/2}$ or $m\ge L^{\Lambda'/2}/(2D_\mu)$. In the first branch the longest spine belongs to a Pre part once $\Lambda'\gg\log\lambda$; its $v_\mu\ell_{\max}/L$ dominates $C\bar\Delta'\Lambda'^{p_2-1}$ when $m-1\le L^{\Lambda'/4}$. If $m-1>L^{\Lambda'/4}$, or in the second branch, $(m-1)\tau_\mu/2$ dominates the polynomial $C(\log m+\Lambda')\Lambda'^{p_2-1}$ and $(m-1)E_\mu$. This proves (B.17). No deposit is required at a point restart; its merge at $q'=\mu$ is the C-01 exception.

**Overflow pure merge.** All inputs are Active/Pending and $\sum_i\nu_i>\nu_{\max}(\mu)$; the output restarts with $\nu'=1,U'=0$. Since $(m-1)\tau_\mu\ge(m-1)E_\mu$, it suffices, conservatively, that
$$\sum_i\nu_i-1\ge\tau_{t^{*\prime}}+W_\mu(t^{*\prime})+1.\tag{B.18}$$
By (B.2), $\ell_i\le\nu_iD_k$ and $\Lambda'\le\log_L(2D_\mu\sum_i\nu_i)$. If $\Lambda'\le\lambda$, the right side of (B.18) is at most $C_r\lambda^{p_2}$ by v3 (4.4), while $\sum_i\nu_i-1\ge\nu_{\max}(\mu)\ge C_\nu\lambda^{p_2}\ge C_r\lambda^{p_2}$. If $\Lambda'>\lambda$, the right side is at most $C\Lambda'^{p_2}$ and $\sum_i\nu_i\ge L^{\Lambda'}/(2D_\mu)\ge C\Lambda'^{p_2}+1$. Thus (B.18) and (B.7) hold. The old banks are discarded, not spent again.

**$R$ and the end of the window.** A removed ripe component has no output obligation. A kept ripe component has old $G\ge\tau_k+\nu+U$ and new $t^*=k+n_q(k)$, $U'=0,\nu'=1$; the numerical requirement is
$$A'_3\lambda_k^{p_R}\ge C_R\lambda_k^{2d+1}+\tau_{k+n_q(k)}
 +\sum_{j=k+1}^{k+n_q(k)}w_j+1-\tau_k-\nu-U.\tag{B.19}$$
It follows from the stronger v3 §4.6 bound, since $p_R>p_2+2d$. At $k_0$, (H-$\lambda$) gives
$$\sum_{j=k_0+1}^{k_f}w_j\le(k_f-k_0)C_w\lambda_{k_f}^{2d+1}
\le\lambda_{k_0}C_w(\tfrac d2\lambda_{k_0}+c_d)^{2d+1}
\le A_2\lambda_{k_0}^{p_2};\tag{B.20}$$
the last inequality holds for large $\lambda_0$ because $p_2\ge2d+3$. Therefore $\tau_{t^*}\ge2A_2\lambda_{k_0}^{p_2}$ pays the flat threshold $A_2\lambda_{k_0}^{p_2}$ and the future $w$ sum; the old $V$ pays the existing spine and waiting costs. The frozen-step proof of §4.7 then applies. This check includes Pending components at $k_0$, because their $t^*>k_0$.

**Status of B.3:** the algebraic counter is proved, conditional on (G1), (G2), (B), (Rg), (K), (H-$\lambda$), and the state/cover lemmas above; confidence high. The within-cap proof uses the stronger $\Lambda'=O(\log\lambda)$ consequence of the cap. Constants must be chosen uniformly when the abstract theorem is formalized.

## C. Path replacement for (3.11)′

### C.1 Exact source domain and a quantitative lattice lemma

P7 (3.11), *Commun. Math. Phys.* **198** (1998), journal p. 522, uses
$$|\partial^1\psi'_{k_1}|<3\delta_{k_1}\quad\text{on }W_{k_1}^{\sim1}\cap U_{k_1}^{\sim4},\qquad
\psi'_{k_1}=e_1\quad\text{on }(U_{k_1}^{\sim3})^c.\tag{C.1}$$
It then estimates $R(\psi_0)\widetilde\psi_{k_1}(x)-\psi_0$ for $x\in\mathbb B_{k_1}(W_{k_1})\cap U_{k_1}^{\sim3}$ by a path in this very domain. The restrictions in (C.1) come from P7 (3.7), not from Lemma S. P5 (1.2)–(1.4), *Commun. Math. Phys.* **196** (1998), journal p. 488, define $U_j=Z_j^{\approx}$ and $W_j=(Z_j^c)^{\approx2}$. In §2 of P7, journal p. 498, Balaban localizes to one component $Z$ by the convention $Z_k=Z$ and suppresses the intersections with $Z$; version 4 must say explicitly whether the $U,W$ in (C.1) are the localized sets for the lineage of that $Z$.

Here is a precise geometric lemma. Let $A=\bigcup_{i=1}^N B_i\subset\mathbb Z^d$ be a union of pairwise $*$-separated, axis-parallel boxes of side at most $b$ in $\pi_q$-cube units; work in a non-winding lift from the torus. Put $a=[R_{q-1}]+1$, $U=A^{\sim a}$, $W=(A^c)^{\sim2a}$, and $D=U^{\sim3}=A^{\sim(a+3)}$. Let $\mathcal C$ be the nearest-neighbour component of $D$ containing $x$, and let $N_{\mathcal C}$ be the number of boxes $B_i$ whose $(a+3)$-neighbourhood meets $\mathcal C$. Then for every
$$x\in\mathbb B_q(W)\cap D$$
there is a nearest-neighbour path $\gamma=(x=x_0,\ldots,x_n)$ in the scale-$q$ unit lattice such that $x_n\in D^c$, every vertex and bond of $\gamma$ lies in $W^{\sim1}\cap U^{\sim4}$ (with the endpoint interpreted in the one-layer collar), and
$$n\le C_d N_{\mathcal C}M(b+a+5)\le C'_d N_{\mathcal C}M\mathrm{crit}_q\quad\text{if }b\le\mathrm{crit}_q.\tag{C.2}$$
The fixed constants absorb the conversion between $\pi_q$ cubes and scale-$q$ sites, and $a\le r_q+1$, $\mathrm{crit}_q=2c_0r_q+10$. One may take an explicit coarse constant such as $C'_d=20(1+c_0)$; optimizing it has no use.

*Proof.* First move from $x$ along a shortest lattice path to $A^c$, stopping earlier if $D^c$ is reached. Since $x\in\mathbb B_q(W)$, the distance to $A^c$ is at most $M(2a+2)$; along a shortest path this distance decreases, so the path stays in $W^{\sim1}$. Until the stopping time it lies in $D$, hence in $U^{\sim4}$. If it reaches $A^c$, choose any two coordinate directions and keep the remaining coordinates fixed. In that two-dimensional slice the nonempty intersections with the boxes are pairwise $*$-separated rectangles of side at most $Mb$. A horizontal ray to the right can be modified each time it first meets a rectangle: from the site immediately before it, follow the one-site outer boundary up to its top, across to its right side, and back to the original horizontal row. The detour stays outside *every* rectangle because their one-site outer boundaries meet no other rectangle. Its horizontal coordinate never decreases; that rectangle is never encountered again. Each detour adds at most $2Mb+O(M)$ vertical steps. Stop at the first exit from $D$. Every site before that exit is in $A^c\cap D\subset W\cap U^{\sim4}$, and the first outside site is in $W\cap U^{\sim4}$ because it is one bond from $D=U^{\sim3}$. Every rectangle encountered before exit belongs to $\mathcal C$; there are at most $N_{\mathcal C}$ of them. The horizontal travel before exit is at most the horizontal diameter of $\mathcal C$ plus one. The union of the $N_{\mathcal C}$ enlarged boxes making $\mathcal C$ is connected, so its horizontal diameter is at most $N_{\mathcal C}M(b+2a+6)$. Add the initial $M(2a+2)$ and the detours to obtain (C.2). $\square$

For a *localized* ripe lineage, take $A=Z_q\cap Z$. Lemma C(e4) gives at most $\nu$ boxes, each critical and pairwise $*$-separated, hence $N_{\mathcal C}\le\nu$ and (C.2) gives the requested $C\nu M\mathrm{crit}_{k_1}$ path **provided (C.1) is available on the localized $W^{\sim1}\cap U^{\sim4}$**. Summing (C.1) along the path gives
$$|R(\psi_0)\widetilde\psi_q(x)-\psi_0|\le3C'_d\nu M\mathrm{crit}_q\,\delta_q.\tag{C.3}$$
The lift condition is automatic for this *local* cluster at ripeness in the admissible torus: if its side is $\mathcal L$ and $ML^{k_f+1}\mid\mathcal L$, then its side in $\pi_q$ units is at least $L^{k_f+1-q}\ge L^{n_q(q)+1}>L\exp(\lambda_q/\alpha)$, whereas the local cluster diameter is $O(\nu\mathrm{crit}_q)=O(\lambda_k^{p_2+2})$ and $\lambda_k=O(\lambda_q)$ by (C-f4) and the increment bound. For large $\lambda_0$ the cluster therefore fits in one lift.
The remaining three terms on P7 p. 522 are unchanged. Since $\nu\le\nu_{\max}(k)=O(\lambda_k^{p_2})$, $M$ is fixed, $\mathrm{crit}_q=O(\lambda_k^2)$, and $q\le k$, the new coefficient is $O(\lambda_k^{p_2+2})$. It fits the already declared chain constant $\widehat W=O(\lambda_k^{w_0})$, because
$$w_0-(p_2+2)=\tfrac12p_2(d-2)+3d-2>0\qquad(d\ge3).\tag{C.4}$$
Thus this geometric replacement does not change $p_R=2p_0-2w_0$.

**Outstanding localization obligation.** If $U_q,W_q$ in (C.1) are interpreted as P5's *global* sets $Z_q^{\approx},(Z_q^c)^{\approx2}$ while $A=Z_q\cap Z$ contains only the ripe lineage, then the preceding application is not justified. Other components of $Z_q$ can enter the same thickened component of $U_q^{\sim3}$, and need not be among the $\nu$ certified core boxes. The local path constructed above can pass through one of those other components, where the *global* $W_q^{\sim1}$ need not supply the derivative bound. Lemma S gives connectivity of the complement of the unthickened local boxes, but neither a global $U$-cluster count nor that gradient restriction. For (C.3) one must prove, from the factorization/localization of P7 (2.6)–(2.9) and the characteristic functions (3.7), that the local operator uses the local $U=(Z_q\cap Z)^{\approx}$ and $W=((Z_q\cap Z)^c)^{\approx2}$ with (C.1) on that local domain; alternatively add and prove a saturation lemma saying that the whole global $U_q^{\sim3}$ component relevant to $Z$ has at most $\nu$ critical box obstacles. A mere change of notation in §3.8 is insufficient. P7's p. 498 convention is evidence for the local reading, but does not by itself verify the several-component characteristic-function transfer.

**Status of C.1:** the lattice path lemma and exponent check are proved, with high confidence. The use of the exact P7 characteristic-function bound after localization is **still open**, with medium confidence that it can be discharged by a source-level factorization argument. Consequently (3.11)′ and LF-4 should remain open. The per-box length $\frac12M\mathrm{crit}_{k_1}+8M$ from v3 must be deleted even if localization is proved.

## D. Restated abstract LF-2 theorem for §4 and §8.1

**Theorem (LF-2, corrected statement).** Fix the typing data, derived functions, and abstract histories of §8.1, with $Z_0=\varnothing$ and the base step $0\to1$ governed by (G1), (G2), and (B), whose old-component sum is empty. Use the state type and deterministic transition rules of B.1, including Pending states, the canonical hull closure, and an $R$ record which acts exactly on ripe Active components. Assume (H-$\lambda$):
$$\theta_-\le\lambda_{j+1}-\lambda_j\le\theta_+\quad(j\ge0),\qquad
k_f-k_0<\lambda_{k_0},\qquad
\lambda_{k_f}\le\tfrac d2\lambda_{k_0}+c_d,$$
as well as (G1), (G2), (B), (Rg), and (K) of §8.1 and $\lambda_0\ge\lambda_*$, where $\lambda_*$ depends only on the fixed typing constants. Then:

1. At each $1\le k\le k_0$, every component of $Z_k$ has $t^*>k$ and satisfies
   $$G_k(Z)\ge\tau_{t^*(Z)}+2\sigma_k\ell(Z)+\sum_{j=k+1}^{t^*(Z)}w_j+\nu(Z)+U(Z).\tag{H6′}$$
   Every component of $Z_k^{\rm pre}$ has the same inequality with $t^*\ge k$. Every ripe pre-$R$ component is Active, has $k_1(k)=q$, and has the box core of Lemma C(e4).
2. At every $k_0\le k\le k_f$, every component of $Z_k$ satisfies
   $$G_k(Z)\ge A_2\lambda_{k_0}^{p_2}+2\sigma_k\ell(Z)+\sum_{j=k+1}^{k_f}w_j.\tag{H6-flat}$$
3. Consequently $G_k(Z)\ge2A_2\lambda_k^{p_2}$ after $R$ for $k\le k_0$, $G_k^{\rm pre}(Z)\ge2A_2\lambda_k^{p_2}+1$ on every ripe pre-$R$ component, and $G_k(Z)\ge A_2\lambda_{k_0}^{p_2}$ in the frozen regime.

The theorem is an *internal counter theorem*. Its hypotheses (G1), (G2), (B), and (Rg) must be discharged for the Balaban flow before its conclusion is used in Def-7. The shape assertion follows from Lemma C4, not from the budget inequality alone. In §4.1 add (H-$\lambda$) verbatim to the axioms; in §8.1 change the abstract history to start with $Z_0=\varnothing$ and replace the old window type by B.1. The proof is B.2–B.3, §4.6, and §4.7. In particular (B.20), which fails without (H-$\lambda$), is the transfer step.

**Status of D:** the corrected LF-2 counter theorem follows from the stated abstract axioms and the preceding budget proof, with high confidence. Its application to LF-4 remains conditional on the localization obligation in C.1 and on the source-level verification of the abstract axioms. This distinction should be retained in the v4 status table.
