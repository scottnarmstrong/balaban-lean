# Ruling on the core scale of a ripe window

## Source evidence and scope

* P6, p. 21, Proposition 3.2(ii), says that a component with $K(Z,A_k\cap Z)=0$ has **an index $k_1<k$** satisfying the covered-window properties and (3.20), $k-k_1>\log(\beta_{k_1}a)$. The printed proposition gives no lower bound on $k_1$. P7, p. 498, §2 invokes precisely this proposition. Its (2.1) already contains $R_{j-1}$ at $j=k_1$; p. 499, (2.6)–(2.7), factors the window down to $T_{k_1}(Z_{k_1},A_{k_1})$; and pp. 503–504, (2.22), starts its cross-scale chain at $j=k_1$. These formulas use a positive core scale unless a separate scale-zero convention is supplied. Thus P6 Proposition 3.2(ii) by itself is **not** a proof of $k_1\ge1$; the endpoint is implicit in P7's use of it.
* [LF-RECONSTRUCTION.md](/home/scott/Balaban/notes/phase1/LF-RECONSTRUCTION.md), Definition I.4.1 and §I.4.4, starts with $Z_0=\varnothing$ and permits $R$ only at $1\le k\le k_0$. Definition I.4.7(5) sets the gain clock $b'=\mu$ when a new cube appears and otherwise takes the maximum over old parts; (T6) resets a kept component to $b=k$. Every component has an old or new seed (§I.4.4, before (T1)). Lemma I.4.13(a) states $b(Z)\le q(Z)$ for an Active or Pending component. Definition I.4.6 makes a component ripe only when it is Active and $t^*(Z)=k$; Lemma I.4.13(f4) identifies its core with $k_1(k)=q(Z)$. Lemma III.1.2(a) uses this identification in Part III.
* The same conclusion follows directly through the merge formula: in (T4), (B.3), $\widetilde q=\max_iq_i$, $t_0\ge\widetilde q+n_q(\widetilde q)$, $T\ge t_0$, and $q'=k_1(T)\ge\widetilde q$. The other transitions create a core $\mu\ge1$ or retain an old positive core. This checks that the `Nat.findGreatest` default value $0$ in the definition of $k_1$ cannot be produced by an admissible component history. It remains possible for the *bare arithmetic function* $k_1(t)$ to equal zero at early $t$.

## Ruling and proof

For every nonempty component $Z$ of $Z_k^{\rm pre}$ in the window regime, its gain clock satisfies $b(Z)\ge1$. Induct on $k$. There is no component at scale zero. At the step $k\to k+1$, a component containing a new cube has $b=k+1\ge1$. Otherwise it has at least one old part, by seed positivity. Each such part has a positive gain clock by induction, or has just been kept by $R^{(k)}$ and has gain clock $k\ge1$. The maximum is positive. This includes hull-created geometry: a hull component still contains an old or new seed.

If $Z$ is ripe, it is Active. Lemma I.4.13(a) gives $1\le b(Z)\le q(Z)$, while Lemma I.4.13(f4) gives $q(Z)=k_1(k)$. Therefore **every ripe window in the Part I history has $k_1(k)\ge1$**. There is no layer-zero case for Lemma III.4.4 (Lemma CH) in this flow. No new hypothesis about $k_1$ belongs in the mathematical statement of that lemma.

The distinction from the printed P6 statement matters: the proof uses the specified Part I history and its gain clock. An abstract witness satisfying only P6 Proposition 3.2(ii) has not thereby been shown positive. If Part III is applied to such an abstract witness, its interface must explicitly require $1\le k_1$ or supply a separate scale-zero analysis.

## Landed Lean route

In `Balaban/LargeField/History/LocalHistory.lean`, `RegionHistory.gain` and `gain_of_new` encode the gain-clock recursion. `FlowBook.lean` supplies `RegionHistory.seed_pos`; `RegionHistory.lean` has no component at zero (`H.F.isEmpty_comp_zero`). Prove a history lemma

```lean
theorem RegionHistory.gain_pos (H : RegionHistory S n R k0 K)
    {k : ℕ} (hkK : k ≤ K) (Z : H.Comp k) : 1 ≤ H.gain k Z
```

by induction as above. In the no-new case use `gain_succ_of_not_new`, `seed_pos` to obtain an old part, and `Finset.le_sup`; the kept branch has $k\ge1$ because `H.Comp 0` is empty. `GainClock.lean` already proves `RegionHistory.gain_le_core` using the floor invariant and the transition rules. `RipeWindow.lean` already stores this conclusion as `RipeWindow.gain_le`, and stores $k_1(k)=q(Z)$ as `RipeWindow.core_k1`. Thus any existing `hW : H.RipeWindow k Z` yields, without a new binder,

```lean
have hq1 : 1 ≤ (H.bk k Z).q :=
  (H.gain_pos hkK Z).trans hW.gain_le
have hk1 : 1 ≤ S.k1 k := by rw [hW.core_k1]; exact hq1
```

This supplies the `hq1` argument currently passed to `path_avoids_obstacles` in `R/ChainWalk.lean` and `exists_chain_of_window` in `R/ChainCH.lean`; their callers can discharge it, or the redundant argument can be removed. The positive-core argument may also be added as a derived lemma of `RipeWindow`, rather than as an independent assumption. `History/WState.lean` (`t4Q`, `t4t0`, `Tmin`, `t4q`), `History/T4.lean` (`k1_le_q'`), and `History/StepMerge.lean` (`T4Facts.Q_le_q`) give a second proof by induction on core scales. `History/K1.lean` (`le_k1`, `k1_mono`) proves the needed inequalities for (B.3). Neither route changes the definition of `Setting.k1`.

## What layer zero denotes

The printed generating-set convention is more specific than the proposed phrase “$\mathbb T\setminus\Omega_1$ at layer zero.” P2, p. 607, (1.2), defines the auxiliary $\Lambda_0=\Omega_1^c\cap\widetilde\Omega_1$; p. 608, (1.3), defines the generating set $\mathbb B_k=\bigcup_{j=1}^k\Lambda_j$, so $\Lambda_0$ is **not** part of that generating set. P5, p. 492, text before (1.20), writes $\Lambda_j=(\Omega_j\setminus\Omega_{j+1})\cap\mathbb T^{(j)}$ for $j=0,\ldots,k$ and sets $\Omega_0=\widetilde\Omega_1$, $\Omega_{k+1}=\varnothing$. Hence its $\Lambda_0$ is the same collar $\widetilde\Omega_1\setminus\Omega_1$ on the fine lattice. The *full complement* $\mathbb T\setminus\Omega_1$ can be called a zero layer when partitioning the entire torus, but that requires the different convention $\Omega_0=\mathbb T$; it is not the printed P2/P5 auxiliary layer. The full complement and the collar have different support.

In Lean, `Balaban/Multiscale/GeneratingSet.lean` constrains `Ω j` only for $1\le j\le k+1$, and `layer j := Ω j \setminus Ω (j+1)` is used as a generating-set layer only for $1\le j\le k$. The history instance has `RegionSeq.OmegaAt 0 = ∅` in `Balaban/LargeField/Region/Generating.lean`, hence `flowGeneratingSet` and `RegionHistory.locGen` have an empty `layer 0`. This is a harmless sentinel for the positive-scale generating set and for Lemma CH, because its core is positive. It is **not** an encoding of P2/P5's nonempty collar $\Lambda_0$, nor of the full complement. A later theorem that actually consumes a zero-scale boundary field must introduce that field explicitly (the P2/P5 collar, or the full complement if its own statement calls for it) and prove its block and boundary properties; changing `OmegaAt 0` globally would alter unrelated history interfaces without helping Lemma CH.
