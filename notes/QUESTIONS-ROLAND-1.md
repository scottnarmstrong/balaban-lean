# Questions for Roland (batch 1, 2026-10-11)

Answers to questions 1–4 of the first round are recorded in `review/ROLAND_ANSWERS.md`. Questions
5–10 are those of `review/FORMALIZATION_ROADMAP.md` §11; 11–12 come from drafting the two main
statements (phase 0, `notes/phase0/surface-v1-for-approval.md`). Paper keys: P1–P9 are the ten
papers you sent (P1 = CMP 167, P2 = CMP 175, P3/P4 = CMP 182, P5 = CMP 196, P6/P7 = CMP 198,
P9 = CMP 199); E10 = Balaban, CMP 122 (1989) 355.

**5. Errata.** Do you know of errata, corrections or unpublished notes for the series, especially
for P6 §3 (the step counter), P7 (the large-field renormalization operation R and the base case
with large fields) and P9 Prop. 3.1?

**6. Constants in P9 Thm 1.1.** Is the intended reading that c, c', ρ₀, ρ₁ depend only on d and N
(not on β)? Our draft takes this reading.

**7. How literally should the large-field method be followed?** The definitions behind P5's
inductive hypotheses (the multi-indices 𝔸_k, the operators 𝕋_k, the functions κ_k, C, K and
admissibility) are not written in one place and must be reconstructed. May we redefine this
bookkeeping where needed (for instance an inductive construction of the histories of large-field
regions, or the representation (1.104) of E10), keeping P7's operation R and the meaning of the flow
theorem? Or is R itself not the point, so that any correct large-field mechanism is acceptable?
(Dimock's φ⁴₃ needs no R because few steps remain after a large field appears; for O(N) with many
remaining steps that fails, so we plan to follow P7.)

**8. P6 Thm 4.** The last inequality of its proof (P6 p. 22),
2p₂(β_{k+K}) − const·(log β_{k+K}a)^{2d+2} > p₂(β_{k+n}) for n ≤ K + log β_{k+K}a,
fails as printed: with p₂(β) = A₂(log β)^{p₂} and β_{k+n} ≈ βL^{(k+n)(d−2)}, the ratio
p₂(β_{k+n})/p₂(β_{k+K}) reaches about (1 + (d−2) log L)^{p₂} at the top of the range. Freezing the
threshold at p₂(β_{k₀}) seems to repair it. Do you agree, or is another reading intended?

**9. Step counter.** P6 Prop. 3.2 cites E10 pp. 383–387, which proves a different, geometric
statement under a slowly running gauge coupling. Is an O(N) proof written anywhere, or is a
reconstruction expected?

**10. Uniqueness.** P0 announces a unique infinite-volume state for ν > 0; the series does not
prove it. Is it wanted, or are limits along a sequence of tori (as in our draft of P9 Thm 1.1)
enough?

**11. Form of the main theorem.** We propose to state "the full RG flow with large fields" as a
statement about the model rather than about Balaban's inductive classes: for β ≥ β₀, every
ν ∈ (0,1] and every torus whose side is divisible by M L^{k_f+1},
log(Z(g)/Z(0)) = ⟨g, h⟩ + Σ_{j=1}^{k_f+1} Σ_x Σ_{X ∋ x} ⟨g(x), T_j(x, X; g)⟩,
where X runs over connected unions of blocks of side M L^j, each T_j(x, X; ·) depends only on g on
X, is analytic in g, is bounded by c₉ L^{−j((d−2)/2+δ)} e^{−κ|X|/(ML^j)^d} (for every κ and c₉, with
L, M, β₀ depending on them), and does not depend on the torus when X does not wind around it
(P7 (4.15)–(4.17), P4 (H.4), (H.7), P9 (4.4)–(4.7)). P7 Thm 5 (every density of the flow lies in
P5's class) would be an internal milestone, stated once the large-field definitions are
reconstructed. Is this the right main statement, or do you want the statement in terms of
Balaban's classes?

**12. Infinite volume.** Our draft of P9 Thm 1.1 takes the infinite-volume limits along the tori
whose side is divisible by q^n, n → ∞ (in the proof q = L and M = L^m), because the method needs
the torus side to be divisible by M L^{k_f+1}. Is that acceptable?
