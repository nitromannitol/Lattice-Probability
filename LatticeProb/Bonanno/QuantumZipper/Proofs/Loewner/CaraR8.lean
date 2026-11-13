/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CaraR8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraR3
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraR5
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraR6
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraR7
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraR8a

/-!
# EXT-CA node R8: `Blueprint.RevMapCaratheodory` is a theorem

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3.R, node **R8** and §4. Assembly of

* R3 (`extExists`): the continuous boundary extension `F` of `revMap W T` with the boundary
  correspondence facts `RevExt` (Carathéodory's theorem in the bounded model, nodes C3–C7);
* RZ (`zero_mem_closure_revHull`): `0` lies in the closure of the hull, so the base of the arc
  is `γ 0 = 0`;
* R1 (`swallowedSet_eq_Icc`) and R4 (`revExt_real_outside`): `F` is the real flow off the
  swallowed interval `[a, b]`;
* R7 (`revExt_zero_eq_tip`): the tip of the arc is `F 0`;
* R5 (`revExt_ends`): `a < 0 < b` and `F a = F b = 0`;
* R6 (`revExt_structure_S`): `F` maps `(a, b)` into the arc, injectively on `[a, 0]` and on
  `[0, b]`, with the same image;
* R8 bookkeeping (`isCaratheodoryRevExt_of_structure`).

References: Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Thm 2.1, Prop. 2.5,
Thm 2.6, pp. 20–24; Lawler, *Conformally Invariant Processes in the Plane* (2005), §4.1, p. 80.
The Loewner-specific steps R5 and R7 are the blueprint's own arguments (DEVIATIONS L-CA-R).
-/

noncomputable section

open Set

namespace QuantumZipper

namespace CaraR

/-- The base point of a simple reverse hull is the driver's start `0` (RZ). -/
theorem arc_base_eq_zero {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T)
    {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Icc 0 1)) (hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H)
    (hK : revHull W T = γ '' Ioc 0 1) : γ 0 = 0 := by
  have h0 := zero_mem_closure_revHull hW hW0 hT
  rw [hK] at h0
  have hcl : closure (γ '' Ioc 0 1) ⊆ γ '' Icc 0 1 :=
    closure_minimal (image_mono Ioc_subset_Icc_self)
      (isCompact_Icc.image_of_continuousOn hγc).isClosed
  obtain ⟨s, hs, hs0⟩ := hcl h0
  rcases eq_or_lt_of_le hs.1 with h | h
  · subst h; exact hs0
  · exfalso
    have := hγH s ⟨h, hs.2⟩
    rw [hs0] at this
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)

/-- **R8.** `Blueprint.RevMapCaratheodory` holds: the reverse Loewner map of a simple hull has
a Carathéodory boundary extension with the two-sided welding correspondence. -/
theorem revMapCaratheodory : Blueprint.RevMapCaratheodory := by
  intro W hW hW0 T hT hK
  obtain ⟨γ, hγc, hγi, hγ0, hγH, hKγ⟩ := hK
  obtain ⟨F, hF⟩ := extExists W hW hW0 T hT γ hγc hγi hγ0 hγH hKγ
  have hγ00 := arc_base_eq_zero hW hW0 hT hγc hγH hKγ
  have htip := revExt_zero_eq_tip extExists hW hW0 hT hγc hγi hγ0 hγH hKγ hF
  obtain ⟨a, b, -, -, hS⟩ := swallowedSet_eq_Icc hW hW0 hT.le
  obtain ⟨ha0, hb0, ha, hb⟩ :=
    revExt_ends extExists hW hW0 hT hγc hγi hγ0 hγH hKγ hF htip hS
  obtain ⟨hleft, hright, htop, hbot⟩ := revExt_real_outside hW hW0 hT hF hS
  obtain ⟨hmid, hinjL, hinjR, hpair⟩ :=
    revExt_structure_S hγc hγi hγH hF hγ00 htip ha0 hb0 ha hb hleft hright htop hbot
  exact ⟨F, isCaratheodoryRevExt_of_structure hW hT hγc hγi hγH hKγ hF hγ00 ha0 hb0 ha hb
    hleft hright hmid hinjL hinjR hpair⟩

end CaraR

end QuantumZipper
