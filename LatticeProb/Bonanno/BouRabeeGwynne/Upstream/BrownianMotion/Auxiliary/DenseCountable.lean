/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.DenseCountable at commit fdb5cad; only the module paths of local imports are changed. -/
/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
/-
Vendored from RemyDegenne/brownian-motion, commit
314f04a34ff75e18fd383917ae7fe7d77beb1b6f.
Adaptation: local import paths only. The original Apache-2.0 license and
authorship are retained; see Upstream/BrownianMotion/PROVENANCE.md.
-/
module

public import Mathlib.Topology.Bases

/-!
# A dense countable subset of a second-countable topological space

-/

@[expose] public section

/-- A countable dense subset of a second-countable topological space. -/
def denseCountable (T : Type*) [TopologicalSpace T] [SecondCountableTopology T] : Set T :=
  (TopologicalSpace.exists_countable_dense T).choose

lemma dense_denseCountable {T : Type*} [TopologicalSpace T] [SecondCountableTopology T] :
    Dense (denseCountable T) :=
  (TopologicalSpace.exists_countable_dense T).choose_spec.2

lemma countable_denseCountable {T : Type*} [TopologicalSpace T] [SecondCountableTopology T] :
    (denseCountable T).Countable :=
  (TopologicalSpace.exists_countable_dense T).choose_spec.1

