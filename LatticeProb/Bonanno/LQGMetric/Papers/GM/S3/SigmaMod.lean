/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.SigmaMod at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs

/-!
# σ-algebras of the field modulo additive constants (D79)

GM = Gwynne–Miller, arXiv:1905.00383v3, `uniqueness-final.tex`. The whole-plane GFF is defined
modulo a global additive constant (GM l. 214), and GM condition on "`h|_{ℂ∖B}` viewed modulo
additive constant" (l. 1200–1205; proof of Lemma 5.4, l. 2801). `IsWholePlaneGFF` only fixes the
mean-zero pairings, so the conditioning σ-algebra of GM Theorem 4.2 (4) is:

* `fieldSigma0On h V` : the σ-algebra of the mean-zero pairings `⟨h, ψ⟩`, `supp ψ ⊆ V`;
* `fieldSigmaClosed0 h K := ⋂_{ε>0} fieldSigma0On h (B_ε(K))` (as `fieldSigmaClosed`, LM l. 164).

Moved here from `Papers/GM/S5/Prop43Out.lean` (P2-M2N) so that `GeoIterateHyp`
(`Papers/GM/S3/Defs.lean`) can use them (decision D79 (1)); since D110 P1 they are defined in
`Blueprint/M2Defs.lean` (`Blueprint.IsHarmPart` uses them) and exported here under the old names.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

noncomputable section

namespace LQGMetric.GM

/- D110 P1: the definitions now live in `Blueprint/M2Defs.lean`; the `GM.` names are aliases of
the Blueprint constants (same declarations, so `unfold`/`simp` lemmas are unchanged). -/
export LQGMetric.Blueprint (fieldSigma0On fieldSigmaClosed0)

end LQGMetric.GM
