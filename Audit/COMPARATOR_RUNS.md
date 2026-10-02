# Comparator runs

The official `leanprover/comparator` was run on every pair in this directory at two commits, `bbe0b90` and `2d30e98`, on two local machines. Each pair was checked twice at each commit: once with the Lean kernel, and once more with the independent `nanoda` kernel enabled (a temporary copy of `comparator.json` with `"enable_nanoda": true`). The committed configurations keep `enable_nanoda` false so that a reproduction needs only three tools.

| Tool | Revision |
|---|---|
| leanprover/comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| leanprover/lean4export | `v4.32.0` (`4e7915201d3f9f04470d9eae002fa695f7cdc589`) |
| Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (v0.1.18; Linux 5.15, Landlock ABI 1 in best-effort mode) |
| ammkrn/nanoda_lib | `6ae1f0cd962f081f6c423454c5da729d841236a7` |

## Run at commit `bbe0b90`

A local machine, with the tool revisions above.

| Pair | Lean kernel | Lean and nanoda kernels |
|---|---|---|
| `Kingman` | passed (94 s) | passed (107 s) |
| `BinomialLocalCLT` | passed (187 s) | passed (223 s) |
| `GFF` | passed (210 s) | passed (257 s) |

## Run at commit `2d30e98`

A second local machine (Linux 6.17), with the same tool revisions.

| Pair | Lean kernel | Lean and nanoda kernels |
|---|---|---|
| `Kingman` | passed (61 s) | passed (73 s) |
| `BinomialLocalCLT` | passed (125 s) | passed (162 s) |
| `GFF` | passed (138 s) | passed (185 s) |

A pass means the comparator printed `Your solution is okay!`: the solution proves a theorem whose statement and full dependency closure match the challenge's, using only the permitted axioms.

## Reproducing a run

To reproduce one pair, build `LatticeProbAudit` and then, from the repository root:

```
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> \
  lake env <comparator>/.lake/build/bin/comparator Audit/LatticeProbAudit/<Pair>/comparator.json
```

with `<Pair>` one of `Kingman`, `GFF` and `BinomialLocalCLT`.
