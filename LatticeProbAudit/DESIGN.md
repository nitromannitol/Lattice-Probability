# Design of the comparator surface

Each headline theorem has a directory here.  The `GFF` directory has four files and
the other two have three, because only the `GFF` challenge defines anything beyond
Mathlib's.

- `Challenge.lean` imports `Mathlib` and nothing else.  It rebuilds from Mathlib
  primitives every object the theorem mentions, states the theorem and ends in a
  single `sorry`.  The `Kingman` and `BinomialLocalCLT` challenges need no
  definition: subadditivity along a map, the binomial probability and the normal
  density are written out in the statement.  The `GFF` challenge rebuilds the
  averaging operator of simple random walk, the killed transition kernel and the
  killed Green function in one vocabulary block, between `VOCABULARY-BEGIN` and
  `VOCABULARY-END`.  This file is the object of trust: a reader checks what it
  says, not how it is proved.
- `SolutionBasic.lean` (`GFF` only, the one pair with a vocabulary block) is a
  verbatim, mechanical copy of the vocabulary block of `Challenge.lean`.  It
  imports only `Mathlib`, so the vocabulary elaborates in the solution exactly as
  in the challenge.
- `Solution.lean` imports the library, together with `SolutionBasic` and the bridge
  in `Support/` where the pair has them, restates the challenge theorem
  byte-for-byte, and proves it from the library's verified statements.
- `comparator.json` names the challenge module, the solution module, the theorem
  and the permitted axioms (`propext`, `Classical.choice`, `Quot.sound`), and
  enables the nanoda replay.

The file under `Support/` is part of the `GFF` solution.  `GFFBridge.lean` identifies
the challenge's definitions with the library's.  The vocabulary copies four
definitions of `LatticeProb/Graph/Basic.lean`, but as new constants, so the
bridge proves each equal to its library counterpart: the averaging operator by
unfolding (`rfl`), the killed transition kernel by induction on time, and the
two Green functions from the kernel.  Only `GFF/Solution.lean` imports it; the
`Challenge` and `SolutionBasic` files stay Mathlib-only, since a library import
inside the vocabulary changes instance elaboration there and breaks the
comparator's constant-by-constant closure check.

The public workflow feeds each pair to
[leanprover/comparator](https://github.com/leanprover/comparator), which
elaborates both statements and requires them to coincide, checks the dependency
closure of the solution theorem against the challenge's over Mathlib, replays the
solution's proof through an independent implementation of the Lean kernel, and
rejects any axiom outside the permitted three.  There is no separate local
statement check: the comparator itself checks each solution statement against its
challenge and the closure against Mathlib.  Nothing a solution imports can change
the statement the reader saw in the challenge; it can only supply a kernel-checked
proof of it.

`check_standalone.sh` elaborates a challenge on its own, with the library's build
options, to confirm that it depends on Mathlib alone, and with `--vocabulary`
checks, for each challenge that has a vocabulary block, that the block is
byte-identical in `Challenge.lean` and `SolutionBasic.lean`.
