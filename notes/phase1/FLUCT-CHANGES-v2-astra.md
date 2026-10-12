# FLUCTUATION v2 change ledger

Source: version-1 `FLUCTUATION.md`, SHA-256 `860d4b39e44d96a21d26d9dad4ef008bfd6ac9281b18537f5b2565b19763fb2a`; independent audit `notes/phase1/FLUCT-AUDIT-astra.md`, SHA-256 `baeda7ea93ace96b95b180ef293787e10b00e00a397c34097ec53137ac3f5b1d`. Line ranges refer to this directory's v2 `FLUCTUATION.md`. The read-only Balaban tree was not changed.

| Finding | Disposition | v2 sections and lines | What remains |
|---|---|---|---|
| FL-A01 | PARTLY REPAIRED | §3.2, lines 421–441; §3.3, lines 479–486 | Star support, covering cost, slit-plane domain, and I-5 input corrected. Instantiate landed `PremisesTerm`/`SumConds` for the actual RG terms and prove the full fluctuation I-5 cover. |
| FL-A02 | DELEGATED | §2.7, lines 347–355; §3.3, lines 449–459 | Prove auxiliary margins, NC and (Vmod); see notes/phase1/VMOD.md (in preparation). |
| FL-A03 | DELEGATED | §3.1, lines 411–416; §5.4, lines 827–828 | Prove P6 Props 2.1–2.2 in the present amended class; see notes/phase1/VMOD.md (in preparation). |
| FL-A04 | PARTLY REPAIRED | §4.2, lines 693–709; §1.5, lines 157–164 | Complex H7 prefactor and late (Λ28′) comparison corrected. The decoupled cover/NC and H7 background estimates still need their named LOC inputs; LFR Lemma IV.1.3 retains the older prefactor and needs a separate downstream update. |
| FL-A05 | REPAIRED | §4.2, lines 693–705 | Empty-intersection labels are assigned to the internal bad-region term before modular size or pre-summation is used. |
| FL-A06 | REPAIRED | §3.4, lines 506–532; §3.5, lines 539–544 | Two-mark use requires $\varepsilon_H\le\varepsilon_{\rm PE}/4$ and the corresponding final $\beta$ threshold; verify that bound in each future observable application. |
| FL-A07 | DELEGATED | §2.8, lines 363–380; §5.2, lines 767–769 | Compute joint $\xi$ derivatives and the scale-sensitive RG error; see notes/phase1/RGFREE.md (in preparation). The scalar chord estimate is retained. |
| FL-A08 | DELEGATED | §5.1–§5.2, lines 749–769 | Compute actual $\varrho_{31}$ and divided $\nu$-free equations before applying `matrixFree`; see notes/phase1/RGFREE.md (in preparation). |
| FL-A09 | PARTLY REPAIRED | §5.1, lines 740–743; §5.3, lines 810–818 | A family premise uses draft Def-6 `ContAtZero`; preservation is proved with common working Cauchy neighbourhoods. Transport from the bare nonempty-open clause and the physical base-family check remain. |
| FL-A10 | REPAIRED | §1.5, lines 157–164; Thm 5.1, lines 729–732 | $\alpha_0,E_0$ are fixed before $\beta_*(\alpha_0,E_0)$; no uniform threshold is claimed. |
| FL-A11 | PARTLY REPAIRED | §1.4, lines 143–153; §1.5, lines 157–164 | Amended $\Xi^c$ input class and landed background-only `i5_background` radii are stated; (DL-gap) is checked in selection order under the explicit landed `ChainNum`/cover margin; its instantiation, full fluctuation and modular I-5 remain OPEN. |
| FL-A12 | REPAIRED | §1.2, lines 82–124; §3.4, lines 506–532 | Finite real $D_\Omega$ on disconnected supports satisfies all-support G1–G3, with one unit of entropy constant; the connected-cover geometry remains the cited premise of Lemma 1.2. |
| FL-A13 | REPAIRED | summary, lines 1–55; status paragraphs, lines 418–420, 717–720, 751–752; §§6.1–6.5, lines 850–954 | No complete I-8/I-9 theorem is labelled proved while VMOD.md, RGFREE.md and the other named inputs remain open. |

The local repairs do not close the full step. In particular, Theorems 3.1, 5.1–5.4 and the complete O-2′ application retain the explicit OPEN dependencies listed in §6.5.
