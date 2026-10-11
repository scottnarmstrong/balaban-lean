# Roland's answers to the roadmap questions

Received 2026-10-11 (relayed by Scott), in reply to `FORMALIZATION_ROADMAP.md` §9
(first version, commit 2f3ba12). Verbatim:

> Some questions, I will have to look into. Easy ones:
>
> 1. Large field is essential. That is the crux of the matter.
> 2. Yes, that's fine
> 3. Yes, that's fine
> 4. Different proofs are fine, in fact encouraged. These are Green's function estimates, which is he probably proved in a strange way.
> 5. / 6. I will look into this.

Questions as asked:

1. Goal: method (pilot for YM) or Goldstone theorem? Is the small-field flow (tier C)
   an acceptable first deliverable, and is the large-field R operation essential?
   → **Large fields are essential, "the crux of the matter".**
2. Restrict to hard spins (λ = ∞), keeping general d ≥ 3, N ≥ 2? → **Yes.**
3. Finite-volume statements on tori (ℤ/ML^nℤ)^d, uniform in n, with infinite volume
   only in the final correlation theorem? → **Yes.**
4. External theory (CMP 96, 89, 122): formalize in full or as frozen interfaces? May
   other proofs of the same bounds replace Balaban's random-walk expansions?
   → **Different proofs are fine and encouraged** (for the Green's function estimates).
5. Errata / copies of the gauge papers. → **Open** (Roland will look into it).
6. Constants in P9 Thm 1.1 depend only on d, N? Why does P9 need λ ≥ λ0?
   → **Open** (Roland will look into it).

## Batch 2 (questions 5–12 of `notes/QUESTIONS-ROLAND-1.md`)

Received 2026-10-11 (relayed by Scott), verbatim:

> 5. I unfortunately do not know about the issue and fix
>
> 6. lambda large is certainly needed, otherwise the main statement is false, so might as well assume it everywhere
> 7. I would say anything that work is okay.
> 8. Seems good.
> 9. I guess reconstruction needed.
> 10. Limits of tori are fine with me.
> 11. I cannot quite see what exactly it means, but it sounds fine.
> 12. That's okay.

Reading (orchestrator):

5. Errata. → **None known to Roland.** The errata ledger `notes/ERRATA.md` stands as our own record.
6. Constants of P9 Thm 1.1 / why λ ≥ λ₀. → **λ large is needed for the theorem; assume it
   everywhere.** Hard spins (λ = ∞) satisfy this, so the frozen roots are unaffected. The other half
   of the question (whether c, c', ρ₀, ρ₁ may be chosen independently of β) is not answered; the
   frozen Root-C keeps the strong reading (ruling S0-Q07).
7. How literally to follow the large-field bookkeeping. → **"Anything that works is okay."** The
   large-field calculus (regions, histories, 𝕋_k, κ_k, C, K, admissibility, and the R operation
   itself) may be redefined or replaced in the phase-1 reconstruction, as long as the frozen roots
   are proved.
8. Repair of P6 Thm 4 (freeze the threshold at p₂(β_{k₀})). → **Agreed.**
9. Step counter. → **Reconstruction needed** (no O(N) proof known to Roland).
10. Uniqueness of the infinite-volume state. → **Not needed; limits along tori are fine.**
11. Form of the main theorem (Root-F). → **Accepted** ("sounds fine"), with a request for a clearer
    explanation; a plain-mathematics statement is posted in the GitHub issue opened for Roland.
12. Infinite-volume limits along tori of side divisible by qⁿ. → **Accepted.**
