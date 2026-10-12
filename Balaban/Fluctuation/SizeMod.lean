/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModDefs
public import Balaban.Fluctuation.SizeModCore
public import Balaban.Fluctuation.SizeModG1
public import Balaban.Fluctuation.SizeModUnion
public import Balaban.Fluctuation.SizeModG4
public import Balaban.Fluctuation.SizeModG5
public import Balaban.Fluctuation.SizeModEntropy

/-!
# The covering size modulo a hole: Definition 1.1 and Lemma 1.2 (FLUCTUATION.md §1.2)

Index of the statements (namespace `Balaban.Fluctuation`; `a = cellSide L m₀ m₁ j = M L^j`).

**Definition 1.1** (`SizeModDefs`): `IsDj` (`𝒟_j`), `OmegaComp`, `DjMod` (`𝒟_j(mod Ω^c)`),
`ModAdmissible`, `dcovModE`/`dcovMod` (`d^cov_j(X mod Ω^c)`), `Yhat` (`Ŷ(S)`), `dOmega`
(`d_Ω(S)`); `dcovMod_of_subset`: for `X ⊆ Ω` it is `treeLenCovOne`.

**Lemma 1.2**:
* (G1) `G1_cellCount`, `G1_card` with `c1 d L = (3 (2L-1))^d`;
* (G2) `G2_X`, `G2_S` with `aEnt d L`, `K0 d L κ₀`;
* (G3) `G3_dcov`, `G3_dOmega` with `cG d L = 2 d L`;
* (G4) `G4_subset`, `G4_siteConnected`, `G4_dOmega_le`, `G4_dOmega_le_mod`;
* (G5) `G5` (`euclDist`).
-/
