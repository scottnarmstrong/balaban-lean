/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgTube
public import Balaban.SmallField.Def6AvgGeom

/-!
# Reynolds averaging over paving offsets: the averaged family and its termwise I-6 premises

CLASS-RULINGS Q-A, "Proof and repair of the centred I-6 symmetry".  For a member of the class:

* `avgFB`: the Reynolds average `|Q|⁻¹ ∑_{q ∈ G_j / H_j} F(r_q⁻¹ s)` of the cut-off term `FB` of
  `T∞` over a fixed system of coset representatives `Quotient.out` of the group `G_j` of the
  level-`j` lattice modulo the paving group `H_j`; `avgFB_act` is its full `G_j`-covariance,
  from the covariance of the individual terms under `H_j` (`FB_act`), and the independence of the
  representatives is `reynolds_rep`;
* `avgB_eq_sum`: it is the sum of the translated terms `ℰ_∞(offs t, X + offs t; c(· - offs t))`,
  `t` ranging over the paving offsets (`exists_summand_rep`);
* `avgFamily`: the averaged centred `ℤ^d` term family (polymers: the polymers of the form `X ∋ 0`
  with an active translate; size: the smallest size of an active translate; term: the extension
  to the tube of `avgB` by complex orthogonal rotations);
* `avgFamily_core`: every field of the termwise I-6 premises except the point-group invariance,
  with the counting constant multiplied by `(L^{m₀+m₁})^d` (`avg_count`);
* `avgPolys_image`, `avgFamily_sym_inv`: the point-group invariance;
* `IsSFFamily.premisesTermAvg`: the termwise I-6 premises `PremisesTerm`.
-/

@[expose] public section
namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter Metric Set

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- The offset vector of a paving offset. -/
def offs {Mb : ℕ} (a : Fin d → Fin Mb) : Site d := fun μ => ((a μ : ℕ) : ℤ)

/-- The translate of a polymer. -/
def shiftFin (t : Site d) (X : Finset (Site d)) : Finset (Site d) := X.image (· + t)

theorem mem_shiftFin {t : Site d} {X : Finset (Site d)} {z : Site d} :
    z ∈ shiftFin t X ↔ z - t ∈ X := by
  simp only [shiftFin, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro h; exact ⟨z - t, h, by simp⟩

theorem sub_mem_of_mem_shiftFin {t : Site d} {X : Finset (Site d)} :
    ∀ z ∈ shiftFin t X, (fun z => z - t) z ∈ X := fun _ hz => mem_shiftFin.1 hz

theorem add_mem_shiftFin {t : Site d} {X : Finset (Site d)} :
    ∀ x ∈ X, (fun x => x + t) x ∈ shiftFin t X := fun x hx => mem_shiftFin.2 (by simpa using hx)

/-- The configuration on the translate `X + t` of a polymer: `c'(z) = c(z - t)`. -/
def shiftCfg (t : Site d) (X : Finset (Site d)) (c : Cfg d N X) : Cfg d N (shiftFin t X) :=
  reCfg (fun z => z - t) sub_mem_of_mem_shiftFin c

theorem reCfg_shiftCfg (t : Site d) (X : Finset (Site d)) (c : Cfg d N X) :
    reCfg (fun x => x + t) add_mem_shiftFin (shiftCfg t X c) = c := by
  ext (p | i)
  · simp [shiftCfg, reCfg_inl]
  · rfl

theorem shiftCfg_rot (t : Site d) (X : Finset (Site d)) (R : Matrix (Fin N) (Fin N) ℂ)
    (c : Cfg d N X) : shiftCfg t X (rotCfgL R X c) = rotCfgL R (shiftFin t X) (shiftCfg t X c) :=
  reCfg_rot _ _ R c

theorem mem_ball_shiftCfg (t : Site d) (X : Finset (Site d)) (i₀ : Fin N) (ν ρ : ℝ)
    (c : Cfg d N X) :
    shiftCfg t X c ∈ ball (refPt i₀ ν (shiftFin t X)) ρ ↔ c ∈ ball (refPt i₀ ν X) ρ :=
  mem_ball_reCfg (X := shiftFin t X) (X' := X) (fun z => z - t) (fun x => x + t)
    sub_mem_of_mem_shiftFin add_mem_shiftFin (fun x _ => by simp) i₀ ν ρ c


/-! ### The groups and the Reynolds average on block states -/

/-- The fine-lattice group of the level `j` lattice `G_j`. -/
abbrev GG (d L j : ℕ) : Subgroup (Equiv.Perm (Fin d → ℤ)) := symZ (L ^ j)

/-- The fine-lattice group of the paving `H_j`. -/
abbrev HH (d L m₀ m₁ j : ℕ) : Subgroup (Equiv.Perm (Fin d → ℤ)) :=
  symZ (L ^ j * L ^ (m₀ + m₁))

/-- `H_j` inside `G_j`. -/
abbrev KK (d L m₀ m₁ j : ℕ) : Subgroup ↥(GG d L j) := (HH d L m₀ m₁ j).subgroupOf (GG d L j)

/-- The coset space `G_j / H_j` (paving offsets and point group) is finite. -/
noncomputable instance fintypeQuot (d L m₀ m₁ j : ℕ) [NeZero L] :
    Fintype (↥(GG d L j) ⧸ KK d L m₀ m₁ j) :=
  haveI := finite_quotient (d := d) (W := L ^ j) (Mb := L ^ (m₀ + m₁))
    (pow_pos (NeZero.pos L) _)
  Fintype.ofFinite _

/-- The action of `G_j` on block states. -/
def actG (L j : ℕ) (g : ↥(GG d L j)) (s : BSt d N) : BSt d N := BSt.act (L ^ j) (g : Equiv.Perm (Fin d → ℤ)) s

section Avg

variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

variable (P β ν a Tm j) in
/-- **The Reynolds average over the cosets `G_j / H_j` of the cut-off term of `T∞`**, on block
states, with the fixed system of coset representatives `Quotient.out`. -/
noncomputable def avgFB (s : BSt d N) : ℂ :=
  reynolds (KK d L P.m₀ m₁ j) (actG (d := d) (N := N) L j) (FB P β ν a Tm j) s

theorem actG_mul (g g' : ↥(GG d L j)) (s : BSt d N) :
    actG L j (g * g') s = actG L j g (actG L j g' s) :=
  BSt.act_mul (pow_pos (NeZero.pos L) j) dvd_rfl g.2 _ s

/-- **The average is invariant under all of `G_j`** (full point-group and offset covariance). -/
theorem avgFB_act (hF : IsSFFamily P β ν a Tm ρd Ek) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {g : Equiv.Perm (Fin d → ℤ)} (hg : g ∈ GG d L j) (s : BSt d N) :
    avgFB P β ν a Tm j (BSt.act (L ^ j) g s) = avgFB P β ν a Tm j s := by
  refine reynolds_act (K := KK d L P.m₀ m₁ j) (act := actG (d := d) (N := N) L j)
    (F := FB P β ν a Tm j) (fun x y s => actG_mul x y s) (fun x hx s => ?_) ⟨g, hg⟩ s
  exact FB_act hF hj1 hjk (Subgroup.mem_subgroupOf.1 hx) s

omit [NeZero L] in
theorem blockOf_symm {g : Equiv.Perm (Fin d → ℤ)} (hg : g ∈ GG d L j) (hW : 0 < L ^ j)
    (x : Fin d → ℤ) : blockOf L j (g.symm x) = blkZ (L ^ j) g⁻¹ (blockOf L j x) := by
  have h := blkZ_spec hW (dvd_refl (L ^ j)) ((symZ (d := d) (L ^ j)).inv_mem hg) x
  exact h

/-- **The action on the states of a configuration**: the state of the polymer `X` with the
configuration `c = c'' ∘ g` goes to the state of the image polymer with the configuration `c''`. -/
theorem act_state {g : Equiv.Perm (Fin d → ℤ)} (hg : g ∈ GG d L j) (i₀ : Fin N) (νj : ℝ)
    (X : Finset (Site d)) (y : Site d) (c'' : Cfg d N (X.image (blkZ (L ^ j) g))) :
    BSt.act (L ^ j) g ⟨X, y,
      fieldInfOf L j i₀ X (reCfg (blkZ (L ^ j) g) (fun _ hx => Finset.mem_image_of_mem _ hx) c''),
      hInfOf νj X (reCfg (blkZ (L ^ j) g) (fun _ hx => Finset.mem_image_of_mem _ hx) c'')⟩ =
    ⟨X.image (blkZ (L ^ j) g), blkZ (L ^ j) g y, fieldInfOf L j i₀ (X.image (blkZ (L ^ j) g)) c'',
      hInfOf νj (X.image (blkZ (L ^ j) g)) c''⟩ := by
  have hW : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hdvd : L ^ j ∣ L ^ j := dvd_refl _
  have hbl : ∀ x, blockOf L j (g.symm x) = blkZ (L ^ j) g⁻¹ (blockOf L j x) := blockOf_symm hg hW
  unfold BSt.act
  rw [BSt.mk.injEq]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · funext x i
    simp only [fieldInfOf]
    by_cases h1 : blockOf L j (g.symm x) ∈ X
    · have h2 : blockOf L j x ∈ X.image (blkZ (L ^ j) g) := by
        refine Finset.mem_image.2 ⟨_, h1, ?_⟩
        rw [hbl, blkZ_blkZ_inv hW hdvd hg]
      rw [dite_eq_left h1, dite_eq_left h2]
      refine congrArg (fun p => c'' (Sum.inl p)) (Prod.ext (Subtype.ext ?_) rfl)
      show blkZ (L ^ j) g (blockOf L j (g.symm x)) = blockOf L j x
      rw [hbl, blkZ_blkZ_inv hW hdvd hg]
    · have h2 : blockOf L j x ∉ X.image (blkZ (L ^ j) g) := by
        intro h
        obtain ⟨b, hb, hbx⟩ := Finset.mem_image.1 h
        apply h1
        rw [hbl, ← hbx, blkZ_inv_blkZ hW hdvd hg]
        exact hb
      rw [dite_eq_right h1, dite_eq_right h2]
  · funext x i
    rfl

/-- **The translate of a state**: the translation by the paving offset `a` carries the state of the
polymer `X` with the configuration `c` to the state of the translate `X + t` with `c(· - t)`. -/
theorem act_state_shift {Mb : ℕ} (a : Fin d → Fin Mb) (i₀ : Fin N) (νj : ℝ)
    (X : Finset (Site d)) (y : Site d) (c : Cfg d N X) :
    BSt.act (L ^ j) (tA (L ^ j) Mb a) ⟨X, y, fieldInfOf L j i₀ X c, hInfOf νj X c⟩ =
    ⟨shiftFin (offs a) X, y + offs a, fieldInfOf L j i₀ (shiftFin (offs a) X) (shiftCfg (offs a) X c),
      hInfOf νj (shiftFin (offs a) X) (shiftCfg (offs a) X c)⟩ := by
  have hW : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  unfold BSt.act
  have hb : ∀ b, blkZ (L ^ j) (tA (L ^ j) Mb a) b = b + offs a := fun b => blkZ_tA hW a b
  have hX : X.image (blkZ (L ^ j) (tA (L ^ j) Mb a)) = shiftFin (offs a) X := by
    unfold shiftFin; exact Finset.image_congr (fun b _ => hb b)
  rw [BSt.mk.injEq]
  refine ⟨hX, hb y, ?_, ?_⟩
  · funext x i
    simp only [fieldInfOf]
    have hgm : tA (L ^ j) Mb a ∈ GG d L j := tA_mem_symZ _ _ a
    have hbi : ∀ b, blkZ (L ^ j) (tA (L ^ j) Mb a)⁻¹ b = b - offs a := by
      intro b
      have := blkZ_inv_blkZ hW (dvd_refl (L ^ j)) hgm (b - offs a)
      rwa [hb, sub_add_cancel] at this
    have hb' : blockOf L j ((tA (L ^ j) Mb a).symm x) = blockOf L j x - offs a := by
      rw [blockOf_symm hgm hW, hbi]
    by_cases h1 : blockOf L j x - offs a ∈ X
    · have h1' : blockOf L j ((tA (L ^ j) Mb a).symm x) ∈ X := by rw [hb']; exact h1
      have h2 : blockOf L j x ∈ shiftFin (offs a) X := mem_shiftFin.2 h1
      rw [dite_eq_left h1', dite_eq_left h2]
      refine congrArg (fun p => c (Sum.inl p)) (Prod.ext (Subtype.ext ?_) rfl)
      exact hb'
    · have h1' : blockOf L j ((tA (L ^ j) Mb a).symm x) ∉ X := by rw [hb']; exact h1
      have h2 : blockOf L j x ∉ shiftFin (offs a) X := fun h => h1 (mem_shiftFin.1 h)
      rw [dite_eq_right h1', dite_eq_right h2]
  · funext x i
    rfl

/-- The cut-off term of `T∞` at the translate `X + offs t` of the polymer, with the configuration
`c(· - offs t)`, centred at `offs t`: the `t`-th summand of the Reynolds average. -/
noncomputable def GEs (P : Consts) (β ν a : ℕ → ℝ)
    (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (j : ℕ) (i₀ : Fin N) (νj : ℝ)
    {Mb : ℕ} (t : Fin d → Fin Mb) (X : Finset (Site d)) (c : Cfg d N X) : ℂ :=
  GE P β ν a Tm j i₀ νj (offs t) (shiftFin (offs t) X) (shiftCfg (offs t) X c)

variable (P β ν a Tm j) in
/-- **The Reynolds average over paving offsets and the point group of the term of `T∞`**, as a
function of the configuration of the centred polymer `X ∋ 0` (before the extension to the tube). -/
noncomputable def avgB (i₀ : Fin N) (νj : ℝ) (X : Finset (Site d)) (c : Cfg d N X) : ℂ :=
  avgFB P β ν a Tm j ⟨X, 0, fieldInfOf L j i₀ X c, hInfOf νj X c⟩

/-- Every coset representative acts on `FB` as a paving offset. -/
theorem exists_summand_rep (hF : IsSFFamily P β ν a Tm ρd Ek) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    ∃ r : (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) → (Fin d → Fin (L ^ (P.m₀ + m₁))),
      ∀ q (s : BSt d N), FB P β ν a Tm j (actG L j (Quotient.out q)⁻¹ s) =
        FB P β ν a Tm j (BSt.act (L ^ j) (tA (L ^ j) (L ^ (P.m₀ + m₁)) (r q)) s) := by
  have hW : 0 < L ^ j := pow_pos (NeZero.pos L) j
  have hMb : 0 < L ^ (P.m₀ + m₁) := pow_pos (NeZero.pos L) _
  have key : ∀ q : ↥(GG d L j) ⧸ KK d L P.m₀ m₁ j, ∃ t : Fin d → Fin (L ^ (P.m₀ + m₁)), ∀ s : BSt d N,
      FB P β ν a Tm j (actG L j (Quotient.out q)⁻¹ s) =
        FB P β ν a Tm j (BSt.act (L ^ j) (tA (L ^ j) (L ^ (P.m₀ + m₁)) t) s) := by
    intro q
    obtain ⟨h, hh, t, ht⟩ := exists_rep hMb q
    refine ⟨t, fun s => ?_⟩
    have hmem : h ∈ GG d L j := symZ_mono hMb hh
    show FB P β ν a Tm j (BSt.act (L ^ j) (((Quotient.out q)⁻¹ : ↥(GG d L j)) : Equiv.Perm (Fin d → ℤ)) s) = _
    rw [Subgroup.coe_inv, ht, BSt.act_mul hW dvd_rfl hmem]
    exact FB_act hF hj1 hjk hh _
  choose r hr using key
  exact ⟨r, hr⟩

/-- **The Reynolds average as a sum of translated terms**: with the representatives `r q` of the
cosets, `avgB X c = |Q|⁻¹ ∑_q ℰ_∞(offs (r q), X + offs (r q); c(· - offs (r q)))`. -/
theorem avgB_eq_sum (hF : IsSFFamily P β ν a Tm ρd Ek) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    ∃ r : (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) → (Fin d → Fin (L ^ (P.m₀ + m₁))),
      ∀ (i₀ : Fin N) (νj : ℝ) (X : Finset (Site d)) (c : Cfg d N X),
        avgB P β ν a Tm j i₀ νj X c = (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ)⁻¹ *
          ∑ q, GEs P β ν a Tm j i₀ νj (r q) X c := by
  obtain ⟨r, hr⟩ := exists_summand_rep hF hj1 hjk
  refine ⟨r, fun i₀ νj X c => ?_⟩
  unfold avgB avgFB reynolds
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hr q, act_state_shift (r q) i₀ νj X 0 c]
  unfold GEs GE
  rw [zero_add]

theorem GE_eq_zero {i₀ : Fin N} {y : Site d} {X' : Finset (Site d)}
    (h : ¬ (InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' ∧ y ∈ X')) (νj : ℝ) (c : Cfg d N X') :
    GE P β ν a Tm j i₀ νj y X' c = 0 := by
  unfold GE FB
  rw [ite_eq_right (fun hs => h ⟨hs.1, hs.2.1⟩)]

section Facts

variable (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N}
  (hne : i₁ ≠ i₀)
include hF hn hne

theorem GE_tubeHyp {y : Site d} {X' : Finset (Site d)}
    (h : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' ∧ y ∈ X') :
    TubeHyp i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)
      (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X') where
  analytic := fun _ hc => GE_analyticAt hF hn h.1 h.2 hc
  rot := fun _ hM hMb _ _ hu hu' hr => GE_rot hF hn hne h.1 h.2 hM hMb hu hu' hr

theorem GEs_tubeHyp {Mb : ℕ} (t : Fin d → Fin Mb) (X : Finset (Site d)) :
    TubeHyp i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)
      (GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) t X) := by
  by_cases h : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j (shiftFin (offs t) X) ∧
      offs t ∈ shiftFin (offs t) X
  · have hT := GE_tubeHyp hF hn hne h
    exact hT.comp (reCfgL (X := shiftFin (offs t) X) (X' := X) (fun z => z - offs t)
      sub_mem_of_mem_shiftFin)
      (fun R c => reCfg_rot (X := shiftFin (offs t) X) (X' := X) (fun z => z - offs t)
        sub_mem_of_mem_shiftFin R c)
      (fun c => mem_ball_shiftCfg (offs t) X i₀ _ _ c)
  · have h0 : GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) t X = fun _ => 0 := by
      funext c; exact GE_eq_zero h _ _
    rw [h0]
    exact ⟨fun _ _ => analyticAt_const, fun _ _ _ _ _ _ _ _ => rfl⟩

omit hne in
theorem GEs_norm_le {Mb : ℕ} (t : Fin d → Fin Mb) (X : Finset (Site d)) {B : ℝ}
    (hB : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j (shiftFin (offs t) X) ∧
      offs t ∈ shiftFin (offs t) X →
        P.E₀ * Real.exp (-P.κ * dInf L m₁ k P.m₀ j (shiftFin (offs t) X)) ≤ B) (hB0 : 0 ≤ B)
    {c : Cfg d N X} (hc : c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X) (liftRadius d L N P j)) :
    ‖GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) t X c‖ ≤ B := by
  by_cases h : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j (shiftFin (offs t) X) ∧
      offs t ∈ shiftFin (offs t) X
  · refine (GE_norm_le hF hn h.1 h.2 ((mem_ball_shiftCfg (offs t) X i₀ _ _ c).2 hc)).trans ?_
    exact hB h
  · unfold GEs
    rw [GE_eq_zero h]
    simpa using hB0

theorem avgB_tubeHyp (X : Finset (Site d)) :
    TubeHyp i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)
      (avgB P β ν a Tm j i₀ (nuIdeal L k (ν k) j) X) := by
  obtain ⟨r, hr⟩ := avgB_eq_sum hF hn.hj1 hn.hjk
  have : avgB P β ν a Tm j i₀ (nuIdeal L k (ν k) j) X = fun c =>
      (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ)⁻¹ *
        ∑ q, GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (r q) X c := by
    funext c; exact hr i₀ _ X c
  rw [this]
  refine ⟨fun c hc => ?_, fun M hM hMb u u' hu hu' hrot => ?_⟩
  · exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun q _ =>
      (GEs_tubeHyp hF hn hne (r q) X).analytic c hc)
  · rw [Finset.sum_congr rfl fun q _ => (GEs_tubeHyp hF hn hne (r q) X).rot M hM hMb u u' hu hu' hrot]

end Facts

end Avg

section Family

variable (L m₁ k) in
/-- **The polymers of the averaged family**: the polymers `X ∋ 0` one of whose translates by a
paving offset is a polymer of `T∞`. -/
def avgPolys (P : Consts) (j : ℕ) : Set (Finset (Site d)) :=
  {X | (0 : Site d) ∈ X ∧ ∃ t : Fin d → Fin (L ^ (P.m₀ + m₁)),
    InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j (shiftFin (offs t) X)}

variable (L m₁ k) in
/-- The offsets `t` for which the translate of `X` is a polymer of `T∞`. -/
def activeOffs (P : Consts) (j : ℕ) (X : Finset (Site d)) : Set (Fin d → Fin (L ^ (P.m₀ + m₁))) :=
  {t | InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j (shiftFin (offs t) X)}

variable (L m₁ k) in
/-- **The size of a polymer of the averaged family**: the smallest size `dInf` of its active
translates. -/
noncomputable def avgDist (P : Consts) (j : ℕ) (X : Finset (Site d)) : ℝ :=
  sInf ((fun t => dInf L m₁ k P.m₀ j (shiftFin (offs t) X)) '' activeOffs (d := d) L m₁ k P j X)

omit [NeZero L] in
theorem avgDist_le {P : Consts} {j : ℕ} {X : Finset (Site d)}
    {t : Fin d → Fin (L ^ (P.m₀ + m₁))} (ht : t ∈ activeOffs (d := d) L m₁ k P j X) :
    avgDist L m₁ k P j X ≤ dInf L m₁ k P.m₀ j (shiftFin (offs t) X) :=
  csInf_le (Set.Finite.bddBelow ((Set.toFinite _).image _)) ⟨t, ht, rfl⟩

omit [NeZero L] in
theorem exists_avgDist_eq {P : Consts} {j : ℕ} {X : Finset (Site d)} (hX : X ∈ avgPolys L m₁ k P j) :
    ∃ t ∈ activeOffs (d := d) L m₁ k P j X,
      avgDist L m₁ k P j X = dInf L m₁ k P.m₀ j (shiftFin (offs t) X) := by
  obtain ⟨-, t, ht⟩ := hX
  have hne : ((fun t => dInf L m₁ k P.m₀ j (shiftFin (offs t) X)) ''
      activeOffs (d := d) L m₁ k P j X).Nonempty := ⟨_, t, ht, rfl⟩
  obtain ⟨t', ht', e⟩ := hne.csInf_mem ((Set.toFinite _).image _)
  exact ⟨t', ht', e.symm⟩

end Family

section Bound

variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

variable (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ : Fin N}
include hF hn

/-- **The bound on the ball**: `|avgB X (c)| ≤ E₀ e^{-κ d(X)}`. -/
theorem avgB_norm_le {X : Finset (Site d)}
    {c : Cfg d N X} (hc : c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X) (liftRadius d L N P j)) :
    ‖avgB P β ν a Tm j i₀ (nuIdeal L k (ν k) j) X c‖ ≤
      P.E₀ * Real.exp (-P.κ * avgDist L m₁ k P j X) := by
  obtain ⟨r, hr⟩ := avgB_eq_sum hF hn.hj1 hn.hjk
  have hE0 := hF.admissible.E₀_nonneg
  have hκ0 := hF.admissible.κ_pos
  have hB0 : 0 ≤ P.E₀ * Real.exp (-P.κ * avgDist L m₁ k P j X) := by positivity
  rw [hr i₀ _ X c]
  have hcard : 0 < Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) := Fintype.card_pos
  have hterm : ∀ q, ‖GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (r q) X c‖ ≤
      P.E₀ * Real.exp (-P.κ * avgDist L m₁ k P j X) := by
    intro q
    refine GEs_norm_le hF hn (r q) X (fun h => ?_) hB0 hc
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hE0
    have := avgDist_le (d := d) (L := L) (m₁ := m₁) (k := k) (P := P) (j := j) (X := X) (t := r q) h.1
    nlinarith
  calc _ = ((Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℝ))⁻¹ *
        ‖∑ q, GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (r q) X c‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ ((Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℝ))⁻¹ *
        ∑ q : ↥(GG d L j) ⧸ KK d L P.m₀ m₁ j, P.E₀ * Real.exp (-P.κ * avgDist L m₁ k P j X) := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => hterm q))
          (by positivity)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

end Bound

section Count

variable {P : Consts} {j : ℕ}

theorem card_shiftFin (t : Site d) (X : Finset (Site d)) : (shiftFin t X).card = X.card := by
  unfold shiftFin
  exact Finset.card_image_of_injective _ (add_left_injective t)

theorem shiftFin_injective (t : Site d) : Function.Injective (shiftFin t : Finset (Site d) → _) := by
  intro X Y h
  ext z
  have := congrArg (fun S => z + t ∈ S) h
  simp only [mem_shiftFin, add_sub_cancel_right, eq_iff_iff] at this
  exact this

/-- **Counting for the averaged family**: the weighted polymer count is at most the number of
paving offsets times the count around one centre. -/
theorem avg_count (hjk : j ≤ k) {κ : ℝ} (hκ : aEnt d L + 3 ≤ κ)
    (F : Finset ↥(avgPolys (d := d) L m₁ k P j)) :
    ∑ X ∈ F, wt κ X.1 (avgDist (d := d) L m₁ k P j X.1) ≤
      ((L : ℝ) ^ (P.m₀ + m₁)) ^ d * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 *
        (Nat.factorial 8 * Real.exp 1) * K0 d L (κ - 2)) := by
  classical
  have hch : ∀ X : ↥(avgPolys (d := d) L m₁ k P j), ∃ t ∈ activeOffs (d := d) L m₁ k P j X.1,
      avgDist (d := d) L m₁ k P j X.1 = dInf L m₁ k P.m₀ j (shiftFin (offs t) X.1) :=
    fun X => exists_avgDist_eq X.2
  choose f hfa hfd using hch
  rw [← Finset.sum_fiberwise F f (fun X => wt κ X.1 (avgDist (d := d) L m₁ k P j X.1))]
  have hbound : ∀ t : Fin d → Fin (L ^ (P.m₀ + m₁)),
      ∑ X ∈ F.filter (fun X => f X = t), wt κ X.1 (avgDist (d := d) L m₁ k P j X.1) ≤
        (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
          K0 d L (κ - 2) := by
    intro t
    set G := F.filter (fun X => f X = t) with hG
    have hinj : Set.InjOn (fun X : ↥(avgPolys (d := d) L m₁ k P j) => shiftFin (offs t) X.1) (G : Set _) := by
      intro X _ Y _ h
      exact Subtype.ext (shiftFin_injective _ h)
    calc ∑ X ∈ G, wt κ X.1 (avgDist (d := d) L m₁ k P j X.1)
        = ∑ X ∈ G, wt κ (shiftFin (offs t) X.1) (dInf L m₁ k P.m₀ j (shiftFin (offs t) X.1)) := by
          refine Finset.sum_congr rfl fun X hX => ?_
          have ht : f X = t := (Finset.mem_filter.1 hX).2
          unfold wt
          rw [card_shiftFin, hfd X, ht]
      _ = ∑ X' ∈ G.image (fun X : ↥(avgPolys (d := d) L m₁ k P j) => shiftFin (offs t) X.1),
            wt κ X' (dInf L m₁ k P.m₀ j X') := by
          rw [Finset.sum_image hinj]
      _ ≤ _ := by
          refine sum_wt_dInf_le_at hjk hκ (offs t) _ fun X' hX' => ?_
          obtain ⟨X, hX, rfl⟩ := Finset.mem_image.1 hX'
          have ht : f X = t := (Finset.mem_filter.1 hX).2
          refine ⟨mem_shiftFin.2 ?_, ?_⟩
          · simpa using X.2.1
          · have := hfa X
            rw [ht] at this
            exact this
  calc ∑ t, ∑ X ∈ F.filter (fun X => f X = t), wt κ X.1 (avgDist (d := d) L m₁ k P j X.1)
      ≤ ∑ _t : Fin d → Fin (L ^ (P.m₀ + m₁)), (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 *
          (Nat.factorial 8 * Real.exp 1) * K0 d L (κ - 2) := Finset.sum_le_sum fun t _ => hbound t
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp

end Count

section Dom

variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

variable (P β ν a Tm j) in
/-- The data extend into the analyticity domain on **every** torus of the sequence on which the
polymer is good. -/
def ExtAll (X' : Finset (Site d)) (ψ h : InfFld d N) : Prop :=
  ∀ n, GoodAt L m₁ k P.m₀ j X' n → ExtN P β ν a Tm j n X' ψ h

theorem ExtAll.extEv {X' : Finset (Site d)} (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    {ψ h : InfFld d N} (hE : ExtAll P β ν a Tm j X' ψ h) : ExtEv P β ν a Tm j X' ψ h := by
  filter_upwards [hX] with n hn using hE n hn

/-- **The bound of the term of `T∞` on data that extend into the analyticity domain on every good
torus**. -/
theorem Einf_norm_le_dom (hF : IsSFFamily P β ν a Tm ρd Ek) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X' : Finset (Site d)} (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') {y : Site d}
    (hy : y ∈ X') {ψ h : InfFld d N} (hE : ExtAll P β ν a Tm j X' ψ h) :
    ‖Einf P.m₀ Tm j y X' ψ h‖ ≤ P.E₀ * Real.exp (-P.κ * dInf L m₁ k P.m₀ j X') := by
  obtain ⟨n₀, hgood₀⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  refine bound_dInf hgood₀ (norm_nonneg _) hF.admissible.κ_pos.le fun n hgood => ?_
  have hsf := hF.torus (torusSeq L P.m₀ n)
  obtain ⟨Ψ, h', hag, hxi⟩ := hE n hgood
  rw [Einf_eq_torus hF.torusIndep hj1 hjk hy hX ψ h (torusSeq L P.m₀ n) hgood.1 hgood.2]
  have hmem := blockPt_mem_Ypoly (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) hjk
    hgood.1 hy
  rw [hsf.localE j _ _ _ Ψ _ h' (fun x hx => ⟨((hag x hx).1).symm, ((hag x hx).2).symm⟩)]
  exact hsf.boundE j hj1 hjk _ _ hgood.2 hmem _ _ hxi

variable (P β ν a Tm j) in
/-- **The data domain of the averaged family**: the configurations `(ψ, b)` such that for every
polymer of the family and every active translate, the induced fields of `ℤ^d` extend into the
analyticity domain on every good torus. -/
def avgDom (i₀ : Fin N) (νj : ℝ) : Set ((Site d → Spin N) × Spin N) :=
  {p | ∀ X ∈ avgPolys (d := d) L m₁ k P j, ∀ t : Fin d → Fin (L ^ (P.m₀ + m₁)),
    InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j (shiftFin (offs t) X) →
      ExtAll P β ν a Tm j (shiftFin (offs t) X)
        (fieldInfOf L j i₀ (shiftFin (offs t) X) (shiftCfg (offs t) X (pack X p.1 p.2)))
        (hInfOf νj (shiftFin (offs t) X) (shiftCfg (offs t) X (pack X p.1 p.2)))}

section DomBound

variable (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ : Fin N}
include hF hn

/-- **The bound of the averaged term on data of the domain** (off the ball). -/
theorem avgB_norm_le_dom {X : Finset (Site d)} {νj : ℝ} {c : Cfg d N X}
    (hc : ∀ t : Fin d → Fin (L ^ (P.m₀ + m₁)),
      InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j (shiftFin (offs t) X) →
        ExtAll P β ν a Tm j (shiftFin (offs t) X)
          (fieldInfOf L j i₀ (shiftFin (offs t) X) (shiftCfg (offs t) X c))
          (hInfOf νj (shiftFin (offs t) X) (shiftCfg (offs t) X c))) :
    ‖avgB P β ν a Tm j i₀ νj X c‖ ≤ P.E₀ * Real.exp (-P.κ * avgDist (d := d) L m₁ k P j X) := by
  obtain ⟨r, hr⟩ := avgB_eq_sum hF hn.hj1 hn.hjk
  have hE0 := hF.admissible.E₀_nonneg
  have hκ0 := hF.admissible.κ_pos
  have hB0 : 0 ≤ P.E₀ * Real.exp (-P.κ * avgDist (d := d) L m₁ k P j X) := by positivity
  rw [hr i₀ _ X c]
  have hcard : 0 < Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) := Fintype.card_pos
  have hterm : ∀ q, ‖GEs P β ν a Tm j i₀ νj (r q) X c‖ ≤
      P.E₀ * Real.exp (-P.κ * avgDist (d := d) L m₁ k P j X) := by
    intro q
    by_cases hI : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j (shiftFin (offs (r q)) X) ∧
        offs (r q) ∈ shiftFin (offs (r q)) X
    · have hE := hc (r q) hI.1
      have hs : Supp P β ν a Tm j ⟨shiftFin (offs (r q)) X, offs (r q),
          fieldInfOf L j i₀ (shiftFin (offs (r q)) X) (shiftCfg (offs (r q)) X c),
          hInfOf νj (shiftFin (offs (r q)) X) (shiftCfg (offs (r q)) X c)⟩ :=
        ⟨hI.1, hI.2, hE.extEv hI.1⟩
      unfold GEs GE FB
      rw [ite_eq_left hs]
      refine (Einf_norm_le_dom hF hn.hj1 hn.hjk hI.1 hI.2 hE).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hE0
      have := avgDist_le (d := d) (L := L) (m₁ := m₁) (k := k) (P := P) (j := j) (X := X)
        (t := r q) hI.1
      nlinarith
    · unfold GEs
      rw [GE_eq_zero hI]
      simpa using hB0
  calc _ = ((Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℝ))⁻¹ *
        ‖∑ q, GEs P β ν a Tm j i₀ νj (r q) X c‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ ((Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℝ))⁻¹ *
        ∑ q : ↥(GG d L j) ⧸ KK d L P.m₀ m₁ j, P.E₀ * Real.exp (-P.κ * avgDist (d := d) L m₁ k P j X) := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => hterm q))
          (by positivity)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

end DomBound

end Dom

section FamilyPrem

variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

variable (P β ν a Tm j) in
/-- **The averaged centred term family of the class at the scale `j`** (CLASS-RULINGS Q-A): the
polymers `X ∋ 0` one of whose paving translates is a polymer of `T∞`, the size the smallest size of
an active translate, and the term the extension to the tube (by complex orthogonal rotations) of the
Reynolds average `avgB` over the cosets of the paving group in the group of the level-`j` lattice. -/
noncomputable def avgFamily (i₀ : Fin N) (νj ρ : ℝ) : TermFamily d N where
  polys := avgPolys (d := d) L m₁ k P j
  dist := avgDist (d := d) L m₁ k P j
  term := fun X c => trickFn i₀ νj ρ (avgB P β ν a Tm j i₀ νj X) c

/-- **`PremisesCore` of the averaged family**: every field of the termwise I-6 premises except the
point-group invariance, with the counting constant multiplied by the number `(L^{m₀+m₁})^d` of paving
offsets. -/
theorem avgFamily_core (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) :
    PremisesCore (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)) i₀ i₁
      (nuIdeal L k (ν k) j) (liftRadius d L N P j) P.E₀ P.κ (diamA d L P.m₀ m₁)
      (((L : ℝ) ^ (P.m₀ + m₁)) ^ d * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 *
        (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2)))
      (avgDom P β ν a Tm j i₀ (nuIdeal L k (ν k) j)) := by
  have hE0 := hF.admissible.E₀_nonneg
  have hsumF : ∀ F : Finset ↥(avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
      (liftRadius d L N P j)).polys,
      ∑ X ∈ F, wt P.κ X.1 (avgDist (d := d) L m₁ k P j X.1) ≤
        ((L : ℝ) ^ (P.m₀ + m₁)) ^ d * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 *
          (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2)) :=
    fun F => avg_count hn.hjk (by linarith [hn.hκ]) F
  have hsum : Summable fun X : ↥(avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
      (liftRadius d L N P j)).polys => wt P.κ X.1 (avgDist (d := d) L m₁ k P j X.1) :=
    summable_of_sum_le (fun X => by unfold wt; positivity) hsumF
  refine ⟨hne.symm, fun X hX => hX.1, ?_, ?_, hsum, hsum.tsum_le_of_sum_le hsumF, ?_, ?_, ?_, ?_⟩
  · intro X hX
    obtain ⟨t, ht, e⟩ := exists_avgDist_eq hX
    show 0 ≤ avgDist (d := d) L m₁ k P j X
    rw [e]
    obtain ⟨n, hn'⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) ht
    exact dInf_nonneg hn.hjk hn'
  · intro X hX x hx
    obtain ⟨t, ht, e⟩ := exists_avgDist_eq hX
    show _ ≤ diamA d L P.m₀ m₁ * (1 + avgDist (d := d) L m₁ k P j X)
    rw [e]
    have h := infPoly_diam2 (P := P) hn.hjk ht (x := x + offs t) (y := offs t)
      (mem_shiftFin.2 (by simpa using hx)) (mem_shiftFin.2 (by simpa using hX.1))
    simpa using h
  · intro X hX
    exact (avgB_tubeHyp hF hn hne X).trickFn_analytic
  · intro X hX c hc
    exact (avgB_tubeHyp hF hn hne X).trickFn_bound (fun c' hc' => avgB_norm_le hF hn hc') hc
  · intro X hX p hp
    show ‖trickFn i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)
      (avgB P β ν a Tm j i₀ (nuIdeal L k (ν k) j) X) (pack X p.1 p.2)‖ ≤ _
    by_cases hT : pack X p.1 p.2 ∈ Tube i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X
    · exact (avgB_tubeHyp hF hn hne X).trickFn_bound (fun c' hc' => avgB_norm_le hF hn hc') hT
    · have : trickFn i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)
          (avgB P β ν a Tm j i₀ (nuIdeal L k (ν k) j) X) (pack X p.1 p.2) =
          avgB P β ν a Tm j i₀ (nuIdeal L k (ν k) j) X (pack X p.1 p.2) := by
        have hnex : ¬ ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
            rotCfgL R X (pack X p.1 p.2) ∈
              ball (refPt i₀ (nuIdeal L k (ν k) j) X) (liftRadius d L N P j) := hT
        unfold trickFn
        rw [dite_eq_right hnex]
      rw [this]
      exact avgB_norm_le_dom hF hn (fun t ht => hp X hX t ht)
  · intro X hX c hc R hR hRb hRc
    exact (avgB_tubeHyp hF hn hne X).trickFn_rot hc hR hRb hRc

end FamilyPrem

section Sym

variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

omit [NeZero L] in
theorem blkZ_fZ {W : ℕ} (hW : 0 < W) (μ : Fin d) : blkZ W (fZ (W : ℤ) μ) = latFlip μ := by
  funext b
  unfold blkZ
  have := bW_fZ hW 1 μ (ibZ W b)
  rw [show ((W * 1 : ℕ) : ℤ) = (W : ℤ) by simp] at this
  rw [this, bW_ibZ hW]
  funext i
  by_cases h : i = μ
  · subst h; simp [fZ_apply, latFlip]
  · simp [fZ_apply, latFlip, h]

omit [NeZero L] in
theorem blkZ_sZ {W : ℕ} (hW : 0 < W) (μ ν : Fin d) : blkZ W (sZ μ ν) = latSwap μ ν := by
  funext b
  unfold blkZ
  rw [bW_sZ, bW_ibZ hW]
  rfl

/-- Every generator of the point group of the lattice is the block map of an element of `G_j`. -/
theorem exists_latGen {r : Site d → Site d} (hr : IsLatGen r) :
    ∃ g ∈ GG d L j, blkZ (L ^ j) g = r := by
  have hW : 0 < L ^ j := pow_pos (NeZero.pos L) j
  rcases hr with ⟨μ, rfl⟩ | ⟨μ, ν, rfl⟩
  · exact ⟨fZ ((L ^ j : ℕ) : ℤ) μ, fZ_mem _ μ, blkZ_fZ hW μ⟩
  · exact ⟨sZ μ ν, sZ_mem _ μ ν, blkZ_sZ hW μ ν⟩

theorem latGen_invol {r : Site d → Site d} (hr : IsLatGen r) (x : Site d) : r (r x) = x := by
  rcases hr with ⟨μ, rfl⟩ | ⟨μ, ν, rfl⟩
  · funext i
    by_cases h : i = μ
    · subst h; simp [latFlip]
    · simp [latFlip, h]
  · funext i; simp [latSwap]

theorem latGen_zero {r : Site d → Site d} (hr : IsLatGen r) : r 0 = 0 := by
  rcases hr with ⟨μ, rfl⟩ | ⟨μ, ν, rfl⟩
  · funext i
    by_cases h : i = μ
    · subst h; simp [latFlip]
    · simp [latFlip, h]
  · funext i; simp [latSwap]

section SymInv

variable (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N}
  (hne : i₁ ≠ i₀)
include hF hn hne

/-- **Point-group invariance of the averaged terms** (the premise `sym_inv` of I-6): the full
`G_j`-covariance of the Reynolds average (`avgFB_act`) and the compatibility of the extension to
the tube with reindexing (`trickFn_comp`). -/
theorem avgFamily_sym_inv {r : Site d → Site d} (hr : IsLatGen r) (X : Finset (Site d))
    (ψ : Site d → Spin N) (b : Spin N) :
    (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).term (X.image r)
        (pack (X.image r) (fun x => ψ (r x)) b) =
      (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).term X
        (pack X ψ b) := by
  obtain ⟨g, hg, rfl⟩ := exists_latGen (L := L) (j := j) hr
  set ρ := liftRadius d L N P j
  set νj := nuIdeal L k (ν k) j
  have hW : 0 < L ^ j := pow_pos (NeZero.pos L) j
  have hinv : ∀ x, (blkZ (L ^ j) g) ((blkZ (L ^ j) g) x) = x := latGen_invol hr
  have hzero : (blkZ (L ^ j) g) 0 = 0 := latGen_zero hr
  have hσ : ∀ x ∈ X, (blkZ (L ^ j) g) x ∈ X.image (blkZ (L ^ j) g) := fun x hx => Finset.mem_image_of_mem _ hx
  have hτ : ∀ x ∈ X.image (blkZ (L ^ j) g), (blkZ (L ^ j) g) x ∈ X := by
    intro x hx
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hx
    rw [hinv]; exact hb'
  set c'' : Cfg d N (X.image (blkZ (L ^ j) g)) := pack (X.image (blkZ (L ^ j) g)) (fun x => ψ ((blkZ (L ^ j) g) x)) b with hc''
  have hc : reCfg (blkZ (L ^ j) g) hσ c'' = pack X ψ b := by
    ext (p | i)
    · simp [reCfg_inl, hc'', pack, hinv]
    · simp [reCfg_inr, hc'', pack]
  -- the average is covariant
  have hav : ∀ c : Cfg d N (X.image (blkZ (L ^ j) g)), avgB P β ν a Tm j i₀ νj (X.image (blkZ (L ^ j) g)) c =
      avgB P β ν a Tm j i₀ νj X (reCfg (blkZ (L ^ j) g) hσ c) := by
    intro c
    unfold avgB
    have := act_state hg i₀ νj X 0 c
    rw [hzero] at this
    rw [← this]
    exact avgFB_act hF hn.hj1 hn.hjk hg _
  have hT := avgB_tubeHyp hF hn hne X
  have hcomp := trickFn_comp hT (reCfgL (X := X) (X' := X.image (blkZ (L ^ j) g)) (blkZ (L ^ j) g) hσ)
    (fun R c => reCfg_rot (blkZ (L ^ j) g) hσ R c)
    (fun c => mem_ball_reCfg (blkZ (L ^ j) g) (blkZ (L ^ j) g) hσ hτ (fun x hx => hinv x) i₀ νj ρ c) c''
  show trickFn i₀ νj ρ (avgB P β ν a Tm j i₀ νj (X.image (blkZ (L ^ j) g))) c'' =
    trickFn i₀ νj ρ (avgB P β ν a Tm j i₀ νj X) (pack X ψ b)
  have e : avgB P β ν a Tm j i₀ νj (X.image (blkZ (L ^ j) g)) = fun c => avgB P β ν a Tm j i₀ νj X
      (reCfgL (X := X) (X' := X.image (blkZ (L ^ j) g)) (blkZ (L ^ j) g) hσ c) := funext hav
  rw [e, hcomp]
  show trickFn i₀ νj ρ (avgB P β ν a Tm j i₀ νj X) (reCfg (blkZ (L ^ j) g) hσ c'') = _
  rw [hc]

end SymInv

omit [NeZero L] in
theorem blkZ_tA_inv {W Mb : ℕ} (hW : 0 < W) (a : Fin d → Fin Mb) (b : Fin d → ℤ) :
    blkZ W (tA W Mb a)⁻¹ b = b - offs a := by
  have hgm : tA W Mb a ∈ symZ (d := d) W := tA_mem_symZ _ _ a
  have := blkZ_inv_blkZ hW (dvd_refl W) hgm (b - offs a)
  have h2 : blkZ W (tA W Mb a) (b - offs a) = b := by
    rw [blkZ_tA hW a]; funext μ; simp [offs]
  rwa [h2] at this

/-- **Closure of the polymer set of the averaged family under the point group**
(the premise `sym_mem` of I-6): if `g ∈ G_j` and a paving translate of `X` is a polymer of `T∞`, then
so is a paving translate of `gX`, by the decomposition `G_j = H_j · {translations}`. -/
theorem avgPolys_image {r : Site d → Site d} (hr : IsLatGen r) {X : Finset (Site d)}
    (hX : X ∈ avgPolys (d := d) L m₁ k P j) (hjk : j ≤ k) :
    X.image r ∈ avgPolys (d := d) L m₁ k P j := by
  obtain ⟨g, hg, rfl⟩ := exists_latGen (L := L) (j := j) hr
  obtain ⟨h0, t, ht⟩ := hX
  have hW : 0 < L ^ j := pow_pos (NeZero.pos L) j
  have hMb : 0 < L ^ (P.m₀ + m₁) := pow_pos (NeZero.pos L) _
  have hdvd : L ^ j ∣ L ^ j := dvd_refl _
  have hgt : tA (L ^ j) (L ^ (P.m₀ + m₁)) t ∈ GG d L j := tA_mem_symZ _ _ t
  obtain ⟨h, hh, t'', hu⟩ := symZ_decomp hMb
    ((GG d L j).mul_mem hgt ((GG d L j).inv_mem hg))
  have hγ : tA (L ^ j) (L ^ (P.m₀ + m₁)) t'' * g * (tA (L ^ j) (L ^ (P.m₀ + m₁)) t)⁻¹ =
      h⁻¹ := by
    have : h = tA (L ^ j) (L ^ (P.m₀ + m₁)) t * g⁻¹ * (tA (L ^ j) (L ^ (P.m₀ + m₁)) t'')⁻¹ := by
      rw [hu]; group
    rw [this]; group
  have hγH : tA (L ^ j) (L ^ (P.m₀ + m₁)) t'' * g * (tA (L ^ j) (L ^ (P.m₀ + m₁)) t)⁻¹ ∈
      HH d L P.m₀ m₁ j := by
    rw [hγ]; exact (HH d L P.m₀ m₁ j).inv_mem hh
  have hIP := InfPoly_act (P := P) hjk hγH ht
  refine ⟨Finset.mem_image.2 ⟨0, h0, latGen_zero hr⟩, t'', ?_⟩
  have hGH : (HH d L P.m₀ m₁ j) ≤ GG d L j := symZ_mono hMb
  have hb : ∀ b, blkZ (L ^ j) (tA (L ^ j) (L ^ (P.m₀ + m₁)) t'' * g *
      (tA (L ^ j) (L ^ (P.m₀ + m₁)) t)⁻¹) b = blkZ (L ^ j) g (b - offs t) + offs t'' := by
    intro b
    rw [blkZ_mul hW hdvd ((GG d L j).mul_mem ((tA_mem_symZ _ _ t'')) hg),
      blkZ_mul hW hdvd (tA_mem_symZ _ _ t''), blkZ_tA_inv hW, blkZ_tA hW]
    rfl
  have himg : (shiftFin (offs t) X).image (blkZ (L ^ j) (tA (L ^ j) (L ^ (P.m₀ + m₁)) t'' * g *
      (tA (L ^ j) (L ^ (P.m₀ + m₁)) t)⁻¹)) = shiftFin (offs t'') (X.image (blkZ (L ^ j) g)) := by
    ext z
    simp only [Finset.mem_image, mem_shiftFin]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hb]
      exact ⟨w - offs t, hw, by simp⟩
    · rintro ⟨x, hx, hxz⟩
      refine ⟨x + offs t, by simpa using hx, ?_⟩
      rw [hb]
      simp [hxz]
  rw [← himg]
  exact hIP

end Sym

/-- **The termwise I-6 premises for the averaged family** (CLASS-RULINGS Q-A): a member of the class
supplies `PremisesTerm` for the Reynolds average over paving offsets and the point group of the
terms of `T∞`: every field of `PremisesCore`, with the counting constant multiplied by the number
`(L^{m₀+m₁})^d` of paving offsets, together with the point-group invariance `sym_mem`, `sym_inv`
(which the unaveraged family `liftInf` does not have). -/
theorem IsSFFamily.premisesTermAvg {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
    {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
    {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
      (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ} {j : ℕ}
    (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N}
    (hne : i₁ ≠ i₀) :
    PremisesTerm (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)) i₀ i₁
      (nuIdeal L k (ν k) j) (liftRadius d L N P j) P.E₀ P.κ (diamA d L P.m₀ m₁)
      (((L : ℝ) ^ (P.m₀ + m₁)) ^ d * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 *
        (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2)))
      (avgDom P β ν a Tm j i₀ (nuIdeal L k (ν k) j)) :=
  (avgFamily_core hF hn hne).toPremisesTerm
    (fun _ hr _ hX => avgPolys_image hr hX hn.hjk)
    (fun _ hr X _ ψ b => avgFamily_sym_inv hF hn hne hr X ψ b)

end Balaban.SmallField.Def6
