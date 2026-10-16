# YMACCOUNT — what the Yang–Mills account says about our blockers

16 October 2026. Source: the public repository
[ethanwsussman/Yang--Mills-LLM-experiment](https://github.com/ethanwsussman/Yang--Mills-LLM-experiment),
commit `e392ef4`. It contains an LLM-written "complete account of Theorem 0", the Yang–Mills continuum
limit along Bałaban's renormalization group: `theorem_0_complete_account_raw_{I,II,III}.tex`
(about 424k lines) and a condensed manuscript, `ym4_manuscript_zeroth_draft.pdf`. Bałaban's Yang–Mills
papers (CMP 95–122) are the ancestors of the O(N) papers P1–P9, so the same constructions recur.
References `I:n`, `II:n`, `III:n` are line numbers in the three `.tex` parts. The account is unrefereed
and many of its statements are marked by the account itself as unproved (its chapter 13, III:111167–111583).
Nothing below is adopted in Lean yet. Labels: SOLVES, SAME GAP (the Yang–Mills papers have the same
omission), ROUTE (a construction we could adapt), NOTHING.

## Blocker 1 (base case, k_f = 0) — ROUTE for item 17(a), (c); NOTHING for 17(b)
* The bare density is one term with no large-field region; the small-field tests are inserted by the first
  step's own decompositions of unity (CMP119 §1 pp. 246–248), not written into the bare density
  (I:50120–50260, I:50600). Inside a level-0 bad region the background is not defined and the raw variables
  are kept, never integrated over (II:86745–86800). This avoids our one-site failure, which comes from
  integrating through bad spins.
* The first-step reserve comes from a high power of the logarithm in the level-0 threshold (I:142628–142645,
  I:1862–1870). Whether P5 makes the same choice at k = 0 is unchecked.
* The case of no renormalization step does not occur there (III:72303).

## Blocker 2 (switch of backgrounds) — ROUTE (partial) + SAME GAP
* Yang–Mills never switches: the current is a free complex variable throughout (I:45237–45330), which
  supports design A0 of `Q13-DECISION.md`. Its own analogue of the domain problem (a larger current radius
  is not contained in the old space) is left open in one case (I:135200–135235, I:135723–135800).
* The collar-alignment point is printed without proof in Yang–Mills as well (CMP99b (3.35), (3.37);
  CMP109 p. 277), and the manuscript says the large-field papers are silent on never-averaged collar bonds
  (ym4 item C13). The account's mechanism: the tests reach every pinned plaquette within 2LMR₁ of the
  region (CMP119 p. 248; I:142592–142700). For O(N) this means extending the P5 (1.19) direction tests over
  the collar the background reads, which changes the large-field sets.

## Blocker 3 (old boundary terms across a new long hole) — SAME GAP + ROUTE; not solved
* Crossings of a large-field component are charged at full length in Yang–Mills too (CMP122b (1.66)–(1.67);
  I:64119–64137). Bałaban's relative-length bound is stated only for terms at their creation; for inherited
  terms the account claims only decay in a tree length (I:61143–61178). The Yang–Mills counterparts of
  P6 p. 34 are printed without proof (CMP119 p. 276; CMP122b p. 375; pp. 378–379).
* Yang–Mills avoids the configuration: completion happens only for small aligned boxes at the R step
  (I:50479–50487), and other boundary terms keep plain domains with plain length (I:12265–12268).
* Route A (the account's repair, its central proposition "proof outstanding", I:61325): each stored term
  carries a label and a set of live pockets; its bound is in the size of the label only; sums of terms
  touching one pocket are charged to that region's volume (I:73704–73800, I:61380–61386). For O(N) this
  needs a per-cell reserve on long retained holes and an alignment at P6 p. 34.
* Route B: plain domains, completing only components removed by R. Open: why P5 (1.33) completes every hole.

## Blocker 4 (gas of removed components and retained holes) — ROUTE (strong)
* In CMP122b (1.90)–(1.91), as the account reads it, clusters are formed on the core: the polymer minus
  the retained components (Bałaban's set X′∖∪Yᵢ), with classes glued by a localization domain having core
  cubes in both (the p. 388 rule) and incompatibility = cores sharing a point (I:20632–20651,
  I:23298–23314). Two labels overlapping only inside a retained component are then not linked; the length
  through that component is never paid. The gas lemma, subadditivity through core contacts and the
  volume-free counting are proved there (I:20757–20925, I:22700–22728, I:21733–21898).
* P7 pp. 527–528 says only that the union of a cluster is "a connected domain", with polymers in
  D_k(mod Ω_k^c ∩ Y_k); the Yang–Mills ancestor suggests connectedness of the cores. To check for O(N):
  retained variables are fixed parameters inside the braces of P7 (3.26); removed-component halos are
  separated from each other and from retained holes; labels contain whole retained holes.

## Blocker 5 (last integral) — SAME GAP; ROUTE only to avoid localizing
* The walk expansion of the inverse constrained covariance is printed without proof in Yang–Mills
  (CMP99b, sentence before (3.132): "analyzed in the same way … we will not repeat"; I:13143–13171).
* The decoupling parameters multiply random-walk terms, one per visited cell, not operator entries;
  stability needs only δ₁M ≥ κ₁ (II:44720–44730, II:46150–46200). This confirms item 18(a).
* The account stops the flow at a last lattice of fixed size, bounds the final integral crudely in the
  volume, and recovers volume-free bounds by the chessboard estimate (II:63964, II:61119). This gives no
  localized final term and relies on a compact integration variable.

## Blocker 6 (local generating sets) — SAME GAP + weak ROUTE
* The Yang–Mills analogue of P3 (4.46)–(4.47) is printed without proof (CMP119 p. 276, (3.43);
  I:53403–53440); the account's re-proof is announced but absent (I:53446–53610).
* Its order of choice takes the large cube M free upward, M ≥ L³M₁ (I:1498–1580); our root constants use
  L = 7, so M = L·M₁ already exceeds 6M₁. It uses two layers of margin rather than one (II:3929–4190),
  as our collar does, and alternatively keeps the ambient generating set and localizes only domains and
  read sets (II:1334–1338).

## Blocker 7 (torus independence) — ROUTE
* Terms with a non-wrapping domain are defined by a fixed formula, built from walk expansions whose
  footprints lie in the domain, evaluated on the lift; no torus operator enters, so they agree exactly on
  all tori (Theorem 4.38, I:58187 ff.). Torus-extracted scalars agree only up to O(e^{−cN/M})
  (II:89912–90045, marked unproved there). Wrapping domains carry the rest.
* A standing floor on the torus at every level, L^{m+K′−i} ≥ L¹¹MŘᵢ (I:57044–57049), matches the
  condition proposed in our item 24 addendum; non-wrapping means a cube of side ≤ s_j/4 (I:57291).
* Small tori are compared by reflection positivity with a bounded, not small, difference (III:72655–72800).

## Follow-ups
1. Blocker 4: refute-first note on core incidence for the P7 gas; sharpen item 16 to "are clusters formed
   after removing the retained components, as in CMP122b pp. 386–388?".
2. Blocker 7: design the last-scale terms by footprint-localized walk expansions (exact on non-wrapping
   domains), with the torus floor; compare with TORUSLAST.
3. Blocker 3: design note comparing route A and route B; add the plain-domain question to item 14.
4. Item 17: ask whether P5 §1 follows the CMP119 first step (tests inserted by the first step).
5. Obtain CMP99b §3, CMP109 §3, CMP119 pp. 246–248 and 275–276, CMP122a pp. 175–192, CMP122b pp. 367–390,
   CMP116 (2.11) to check the account's readings on the pages.
