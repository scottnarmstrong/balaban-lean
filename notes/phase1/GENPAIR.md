# GENPAIR: a consecutive level pair for general $d,L$

Read-only source: `/home/scott/Balaban/Balaban` at commit `340e13e` (2026-10-13). The names proposed below are **OPEN** until added to Lean. **PROVED** refers only to named declarations already present, or to their stated elementary specialization. The main output is a pair satisfying the *named hypothesis* `hpair` of `tower_core_rates_general_of_pair`; that theorem does not construct the pair.

## T1. Fields and numerical origins

**PROVED (source inspection).** `Localization/Decoupled.lean:137` defines `DGSetting G a ν` with these ten fields. `Localization/Decoupled2.lean:116` defines `Dec2.OpSetting H a ν` with the six fields in the last column. The proofs at `Fluctuation/InteractionLevelPair.lean:469,499`, `Fluctuation/Prop33CloseWitness.lean:68,74`, and `Inhabited/LevelStepSetting.lean:148,182` have the following dependency pattern:

| Field | General proof or numerical obligation | `OpSetting` |
|---|---|---|
| `hd : 3 ≤ d`, `hL : 3 ≤ L` | Parameters; the fixed witness uses `le_rfl` twice. | same |
| `aligned : CubeAligned G m₁` | `levelGS` at the top level: `two_le` from $m_1\geq4$, `dvd` from the torus factor $L^{m_1}$, `union` because each relevant top layer is the whole torus (`lvTopG_Ω`). No dimension-specific constant. | absent |
| `hM : 4 L² ≤ L^{m₁}` | The `36` in the fixed proof is $4\cdot3^2$; $m_1\geq4$, $L\geq3$ suffice since $L^{m_1}\geq L^4\geq4L^2$. | absent |
| `cover_sep : 4dL L^{m₁} ≤ ϱ` | The coefficient `36` in `rhoSep` is $4\cdot3\cdot3$. This is the separation used by `CubeRegimes`, `CoverBase`, and `RowInHat`. | absent |
| `sep : 2d log L ≤ (agmonRate d/16)(ϱ−1)` | The term $6\log3/(\operatorname{agmonRate}(3)/16)$ uses $6=2d$ at $d=3$. `agmonRate_pos` holds for positive $d$; a general formula may divide by it. | same |
| `weights : IsAdmissibleWeights K a` | `isAdmissibleWeights_compWeight` is general with $L\geq3$, $a_1=1$. | same |
| `mass : 0 ≤ ν`, `massLe : ν L^{2K} ≤ 1` | Inputs on $\nu$; `dgSettingNu` uses $\nu=1/81=3^{-4}$ at $K=2$, while `dgSetting_lv` allows every $0\leq\nu\leq3^{-2(k+1)}$. | same |
| `big : 5 < N₁` | The fixed witness has $N_1=9$; the step theorem takes `hN` explicitly. `BoxCube.torusSide_ge` needs $6L^{j+m_1}\leq N_1L^{m_1+K}$ for $j\leq K$, then `box_eq_cubeSet` treats the width-$5L^{j+m_1}$ interaction box without wrap. | absent |

**PROVED.** `Localization/I5Inhabited.lean:216` defines
\[
 \rho_{3,3}(m_1)=\operatorname{bgR0}(3,3)+36\,3^{m_1}+324\,3^{m_1}
 +1+\frac{6\log3}{\operatorname{agmonRate}(3)/16}.
\]
`rhoSep_ge` (`:242`) drops the nonnegative `bgR0` term. The `324` is $4dL^3$ at $(3,3)$: it is the radius `r₀ := 324` of the older I-5 `BgSetting` witness, whose fields `hr₀ : 4dL³ ≤ r₀` and `hr : r₀ L^{m₁} ≤ ϱ−1` occur in `Localization/I5Fan.lean:62`. It is surplus for **just** `DGSetting`, `OpSetting`, and `BgHyp`; keeping it makes the general separation reproduce the old witness's two radius inequalities. It is not a second independent cover-separation theorem.

**PROVED.** `Localization/MooreDegree.layer_not_near` (`:93`) assumes $d\leq\rho L^2$ for two layers at least two apart. This follows from `cover_sep` when $L\geq3$, $m_1\geq4$: $\rho\geq4dL^{m_1+1}\geq d$ and $L^2\geq1$. The landed `Fluctuation/DetCauchyGraph.d_le_of_cover_sep` (`:822`) is exactly this implication. No new large-$L$ hypothesis is hidden there.

**REFUTED as a description of the present cover.** The side $(2L-1)L^{m_0}$ is *not* the current `DGSetting.big` requirement. `Decoupled.intBox` has half-width $(5/2)L^{j+m_1}$ for every $L$, and `BoxCube.torusSide_ge` uses a six-cell bound. Its exact general threshold is $N_1\geq6$ (`5 < N₁`), independent of $d,L$. If a **different** cover were redefined with side $(2L-1)B$ and the same one-$B$ no-wrap margin, its analogue would be $N_1\geq2L$; that would require redoing the cover proofs and constants. No such change is needed for the level pair.

## T2. Explicit general pair and statements

**OPEN definition, with proved inequalities.** For $d,L\geq3$, set $r_G(d,L)=4dL^3$ and define the conservative separation
\[
 \boxed{\rho\operatorname{SepG}(d,L,m_1)=\operatorname{bgR0}(d,L)
 +4dL\,L^{m_1}+r_G(d,L)L^{m_1}+1
 +\frac{2d\log L}{\operatorname{agmonRate}(d)/16}.}
\]
All summands except the displayed `1` are nonnegative for $d,L\geq3$: `bgR0` is a maximum containing $4dL$, $\log L>0$, and `agmonRate_pos` supplies the denominator. Consequently it satisfies simultaneously `bgR0 d L ≤ ρSepG`, `4dL L^m₁ ≤ ρSepG`, $2d\log L\leq(\operatorname{agmonRate}(d)/16)(\rho\operatorname{SepG}-1)$, $r_G L^{m_1}\leq\rho\operatorname{SepG}-1$, and $4dL^3\leq r_G$. Thus it covers the three pair setting separations and the optional old I-5 radius separation. At $(d,L)=(3,3)$ it reduces arithmetically to `rhoSep m₁` ($36$, $324$, $6\log3$).

**OPEN definitions, immediate from landed `levelGS`.** For $k\geq1$, $N_1\geq6$, $m_1\geq4$, and $\rho=\rho\operatorname{SepG}(d,L,m_1)$, use the already landed abbreviations in `Inhabited/LevelStepSettingGeneral.lean:41,46`:

```lean
GpG d L N₁ m₁ k := lvTopG d L N₁ m₁ k (rhoSepG d L m₁)
HmG d L N₁ m₁ k := lvLowG d L N₁ m₁ k (rhoSepG d L m₁)
```

These are respectively `levelGS` of levels $k+1$ and $k$ on the *same* torus of side $N_1L^{m_1+k+1}$. `isLevel_lvTopG` and `isLevel_lvLowG` prove their levels; no self-pair is substituted. All proposed declarations below have `{d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ν : ℝ}` as ambient binders; their remaining hypotheses are shown explicitly.

```lean
-- OPEN; all at a₁ = 1 and ρ = rhoSepG d L m₁.
theorem dgSetting_lvG (hd : 3 ≤ d) (hL : 3 ≤ L) (hm : 4 ≤ m₁)
    (hN₁ : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) :
  DGSetting (GpG d L N₁ m₁ k) (compWeight L 1) ν
theorem opSetting_lvG (hd : 3 ≤ d) (hL : 3 ≤ L) (hm : 4 ≤ m₁)
    (hN₁ : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) :
  Dec2.OpSetting (HmG d L N₁ m₁ k) (compWeight L 1) ν
theorem hatConn_lvTopG (hL : 3 ≤ L) : HatConn (GpG d L N₁ m₁ k)
theorem rowInHat_lvG (hk : 1 ≤ k) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hm : 4 ≤ m₁) (hN₁ : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) :
  RowInHat (coverOf (GpG d L N₁ m₁ k)) (HmG d L N₁ m₁ k)
    (compWeight L 1) ν
theorem coverBase_lvG (hk : 1 ≤ k) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hm : 4 ≤ m₁) (hN₁ : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) :
  Dec2.CoverBase (coverOf (GpG d L N₁ m₁ k)) (HmG d L N₁ m₁ k)
    (compWeight L 1) ν (levelKc d L) (Cchi d L)
theorem footLocal_lvG (hk : 1 ≤ k) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hm : 4 ≤ m₁) (hN₁ : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) :
  Dec2.FootLocal (coverOf (GpG d L N₁ m₁ k)) (HmG d L N₁ m₁ k)
    (compWeight L 1) ν (levelKc d L) (Cchi d L)
theorem flCore_lvG_nonempty (N : ℕ) (hk : 1 ≤ k)
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hm : 4 ≤ m₁)
    (hN₁ : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1)
    {c BG κ c₂ BG₂ : ℝ} (hS : DecSpecs d L c BG) (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hS2 : Dec2.DecSpecs d L (levelKc d L) (Cchi d L) c₂ BG₂)
    (hM2 : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) :
  ∃ t : ℝ, 0 < t ∧ Nonempty
    (FlCore N (GpG d L N₁ m₁ k) (HmG d L N₁ m₁ k)
      1 ν c BG κ t (levelKc d L) (Cchi d L) c₂ BG₂ t)
```

This is a signature template, not elaborated Lean code: the displayed ambient binders and `GpG`/`HmG` abbreviations must be declared in the module. `hatConn_lvTopG` only needs a positive $L$ large enough that `hatRad L m₁ j ≥ 1`; $L\geq3$ is a convenient sufficient hypothesis and it does **not** need $m_1\geq4$, $N_1\geq6$, or mass bounds. All other `*_lvG` signatures mirror their landed $(3,3)$ versions, with $4L^2\leq L^{m_1}$ and $N_1\geq6$ providing their geometric side conditions.

**PROVED conditional on the OPEN `dgSetting_lvG` and `opSetting_lvG` settings.** `rowInHat_level`, `coverBase_level`, `footLocal_level`, and `flCore_level_nonempty` are already general in $d,L,N$ in `InteractionLevelPair.lean:200,205,212,318`. Apply them to the two `IsLevel` proofs, `bgHyp_lvG` (`LevelStepSettingGeneral.lean:157`, using `bgR0≤rhoSepG`), and the displayed setting fields. `hatConn_lvTopG` repeats `hatConn_lvTop` (`LevelStepSetting.lean:197`) with `lvTopG_Ω`, `hatRad`, and `boxSet_connected`; it uses no decoupling estimate. `hatStepKG` and `hatStepKG_betaU` are already landed (`LevelStepSettingGeneral.lean:75,99`) for $N\geq2$; the latter gives $\beta_U=\beta L^{k(d-2)}$. There is no need to reconstruct the step setting.

**OPEN one-line `hpair` instance after the first two settings.** Fix $N_1=9$, $K=2$, $a_1=1$, arbitrary $N$ and $0\leq\nu\leq L^{-4}$ (equivalently $\nu L^4\leq1$). For every $m_1\geq4$, let `ϱ m₁ := rhoSepG d L m₁`, `ϱm := ϱ`, `Gp m₁ := GpG d L 9 m₁ 1`, `Hm m₁ := HmG d L 9 m₁ 1`, and choose `n := 1`. The two setting declarations, `isLevel_lvLowG`, `isLevel_lvTopG`, and `bgHyp_lvG` supply exactly the five conjuncts of `hpair` in `tower_core_rates_general_of_pair` (`TowerCoreRatesGeneral.lean:43`). The tower theorem then proves its 21 output clauses for every $\kappa_{\min}$ under its stated $\kappa_0,\kappa_{\rm dec}$ inequalities. Without this instance, those 21 clauses remain conditional on an OPEN pair assertion.

## T3. Parity and size of $L$

**PROVED for this interface.** Neither `DGSetting`, `Dec2.OpSetting`, `levelGS`, `hatRad`, the fixed width-$5B$ cover, nor `boxSet_connected` asks that $L$ be odd. `agmonRate_pos` requires $d>0$, not $L$ large relative to $d$. The Moore-degree inequality follows from the chosen $\rho$ for every $d,L\geq3$. The only scale comparison in these settings is $4L^2\leq L^{m_1}$, already guaranteed by $m_1\geq4$. No $L_0(d)$ is needed for the **pair**.

**PROVED separate downstream restriction.** The centred determinant-collar reflection identity in `Fluctuation/DetCollarCentered.lean` and its fibre version use $L=2q+1$; this is an odd-$L$ condition on that later symmetry argument, not on the level pair. For a root theorem that can choose $L$ after $d,N,\kappa,c_9$, the clean interface is to choose **any sufficiently large odd $L\geq3$ required by the later estimates**, then choose $m_1\geq4$ and $\rho=\rho\operatorname{SepG}(d,L,m_1)$. If the later proof uses no parity-dependent collar symmetry, $L\geq3$ alone suffices here. The pair construction should not bake in an unspecified $L_0(d)$ or a fixed $L=3$.

## T4. Ordered bounded worker targets

1. **Start immediately; transfer of landed $(3,3)$ proof, Sonnet suitable; ≤220 new lines.** Add `rhoSepG`, its five inequalities and $(3,3)$ specialization, `GpG/HmG`, `dgSetting_lvG` and `opSetting_lvG`. Prove `hM` by $L^4\geq4L^2$, `sep` by positive multiplication, `aligned` by `lvTopG_Ω`. This is the only analytic-free prerequisite for `hpair`.
2. **Start immediately; transfer, Sonnet suitable; ≤220 new lines.** Add `hatConn_lvTopG`, `rowInHat_lvG`, `coverBase_lvG`, `footLocal_lvG`, and `flCore_lvG_nonempty` with the precise signatures above. The last four are applications of already general `*_level` declarations; this worker can import the first worker's signature or use `DGSetting`/`OpSetting` as temporary explicit inputs, then specialize once target 1 lands.
3. **After target 1; ≤100 new lines.** Construct the fixed $K=2$, $n=1$, $N_1=9$ `hpair` and invoke `tower_core_rates_general_of_pair`. State the mass range and all rate assumptions explicitly; do not claim an unconditional tower before `hpair` is present.
4. **Later downstream bridge; ≤300 new lines per module.** Connect odd-$L$ `detCollarHullC` symmetry and `detRateG` to the new tower where required; keep the parity assumption here, downstream of the pair. Check any root theorem's separate $L$ and $N$ inequalities before claiming its final quantifier order.
