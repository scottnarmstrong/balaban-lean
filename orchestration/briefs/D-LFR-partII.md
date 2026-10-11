# Brief D-LFR-II — reconstruction document, Part II (analytic objects, operators, Def-7)

You are the author of the large-field reconstruction document (Lean formalization of Balaban's RG
analysis of the low-temperature O(N) model, hard spins, $d\ge3$). Repository /home/scott/Balaban
(read AGENTS.md first). You write mathematics; you do not write Lean.
**Do not launch subagents (no Agent tool); work directly.**

## Input
- `notes/phase1/LF-RECONSTRUCTION.md` Part I (commit e2c83ae; your own text — keep it unchanged
  except for errors you find, listed explicitly) and `LF-ARCHITECTURE.md` v4 (§§3, 5, 8, 9 outline
  Part II: II.1 running constants vs λ̂; II.2 background fields (∃!); II.3 analyticity spaces and
  characteristic functions; II.4 LF-1; II.5 operators, Lemma F, κ, C, Lemma B, (D5) for a step;
  II.6 Def-7; II.7 LF-6 comes after Part III).
- `notes/phase1/LEMMA-F-astra.md`: paste-ready conditional Lemma F, choice (b): exact factorization
  holds for a **localized representation** built from the I-4 decoupled family; the raw density has
  inter-component interactions carried by the boundary terms 𝓑 with the H7 bound (F.3). Check it
  before adopting; record changes.
- Phase-1 documents now available: `BACKGROUND.md` v2 (I-1, I-2, Def-5 predicates; landed Lean:
  `Balaban/Background/*` incl. `prop51_exists_unique`, `lemma53`, `composeField`,
  `linearResponse`), `LOCALIZATION.md` v2 (I-4, I-5, Option A; landed `Balaban/Localization/*`:
  `abstract_expansion`), `SMALLFIELD.md` v2 (Def-6 = small-field part of Def-7; free flow
  c = a_{k+1}b; Ξ, Ξ^c at λ = ∞), `GREEN.md`, `POLYMER.md`; reviews of all of these.
- Open items to close or carry: Part I O-2 (Lemma F), O-4 (range of P3's minimal generating sets),
  O-6 (Lemma B after hulls and at k = 0; base rule), O-8 (c = 0 vs c = a_{k+1}b in Def-7 (D2), LF-3,
  P7 (2.10)–(2.12), (2.53)–(2.58)).

## Task
Write **Part II, sections II.1–II.6**, appended to `notes/phase1/LF-RECONSTRUCTION.md`, at the same
standard as Part I: closed definitions as functions of explicitly typed data, complete proofs or
explicitly marked citations, constants as explicit functions, every UNCERTAIN marked. Def-7 must be a
predicate `IsRep_k` on representations (v4 design decision), with every object it uses defined or
cited to a landed Lean definition/theorem by name. End with the Lean declaration list for Part II
(dependency order, sizes) and an updated open-items list.

Standards: exact page/equation references to P1–P7, E9/E10; plain mathematical prose; avoid
"calibration", "robust", "leverage", "crucially". Write only `notes/phase1/LF-RECONSTRUCTION.md`
(append; scratch under /tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/lfr2/ allowed); do not commit; do not run Lean.
Write section by section as you go. Reply with: the list of Part II definitions and lemmas (one line
each, with status), changes to Part I or v4, and open items.
