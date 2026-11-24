# bali-lean

Lean 4 / Mathlib formalizations accompanying research papers by Mohammad Bali (ORCID 0009-0000-9606-3628).
No file contains `sorry`; every `#print axioms` line reports only `propext`, `Classical.choice`, `Quot.sound`.

## Contents

- `lean/GappedPfaffian.lean` — gapped Pfaffians (Stages 1-10): 114 `#print axioms` lines.
  Build log: `logs/lean_check_paper7_stage10_2026-11-23.log`.
- The remaining files in `lean/` — skew-orthogonal proofs of binomial Mehta-type sums (section below).

To build `GappedPfaffian`: follow the build steps below, then `lake env lean P699/GappedPfaffian.lean`.

---

# Lean 4 proofs for "Skew-orthogonal proofs, formally verified, of binomial Mehta-type sums at beta = 1"

Toolchain: `leanprover/lean4:v4.36.0-rc2`, Mathlib `v4.36.0-rc2`.

## Build (Linux / WSL / macOS)

The modules are named `P699.*`, so the files must sit in a folder `P699/` of a Lake project whose library is
`P699`.  The files `lakefile.toml` and `lean-toolchain` in this archive define that project.

```bash
# needs elan (https://github.com/leanprover/elan) and git
unzip bali_lean_library.zip -d bali && cd bali
mkdir -p P699 && cp lean/*.lean P699/
lake exe cache get          # downloads the prebuilt Mathlib (about 5 GB on disk)
lake build P699.ZonotopePaper
```

The root file `ZonotopePaper.lean` imports everything and ends with one `#print axioms` line for each statement
cited in the paper.  Expected output for every name: `propext`, `Classical.choice`, `Quot.sound` only.
No file contains `sorry`.

## Statements cited in the paper

| Paper | Lean |
|---|---|
| Main formula, all d >= 2, n >= d-1 | `Bali.ZF.main_theorem`, `Bali.ZF.small_two` |
| Type B (Brent-Krattenthaler-Warnaar, Prop. 5.3), every d | `Bali.UN.conjB_odd_all`, `Bali.UN.conjB_even_all` |
| Even n: the three relations | `Bali.VE.V_base`, `Bali.VE.V_oddstep`, `Bali.VE.V_ratio` |
| Second Laguerre parameter | `Bali.BP.Bplus_odd`, `Bali.BP.Bplus_even` |
| Watson sum, totals of the Racah polynomials | `Bali.Watson.S_even`, `Bali.TW.T_R` |
| Real n: absolute convergence, value for d even / odd | `Bali.GAbs.summable_V`, `Bali.GE.even_value`, `Bali.GO.odd_value` |
| Carlson's theorem (polynomial growth) | `Bali.Carlson.carlson` |


Not formalized: complex n in the series, the Meixner finite-part theorem, the correlation-function
proposition and the collapse lemma.  These are proved in the paper and checked in exact arithmetic by the
Python scripts published with it.
