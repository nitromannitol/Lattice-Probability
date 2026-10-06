# Comparator runs

The recorded runs below cover exactly `Kingman`, `GFF` and `BinomialLocalCLT`. The official `leanprover/comparator` ran with the Lean kernel and independent `nanoda` kernel enabled. The newly configured `BerryEsseen` and `NormalComparison` pairs have no completed run asserted by this historical table; each requires its own actual recorded result. Every committed configuration enables nanoda.

| Tool | Revision |
|---|---|
| leanprover/comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| leanprover/lean4export | `v4.32.0` (`4e7915201d3f9f04470d9eae002fa695f7cdc589`) |
| Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (v0.1.18) |
| ammkrn/nanoda_lib | `6ae1f0cd962f081f6c423454c5da729d841236a7` |

A pass means the comparator printed `nanoda kernel accepts the solution`, `Lean default kernel accepts the solution` and `Your solution is okay!`: the solution proves a theorem whose statement and full dependency closure match the challenge's, using only the permitted axioms.

## `Kingman`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (77 s) |

## `GFF`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (234 s) |

## `BinomialLocalCLT`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (276 s) |

To reproduce one pair, build `LatticeProbAudit` and then, from the repository root:

```
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator LatticeProbAudit/<Pair>/comparator.json
```

with `<Pair>` one of `Kingman`, `GFF` and `BinomialLocalCLT`.
