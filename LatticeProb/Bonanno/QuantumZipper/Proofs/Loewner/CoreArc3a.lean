/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CoreArc3a at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CoreArc2
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.HullBasics

/-!
# CORE_ARC, part 3a: easy properties of the tip parameter `arcTime`

Plan node CORE of `blueprint/CORE_ARC_PLAN.md` (first part of CoreArc3; continuity of `arcTime`
and tip convergence are *not* here). Companion of `CoreArc2.lean`, which defines
`arcTime A γ r = sSup {u ∈ Ioc 0 1 | γ u ∈ fwdHull A r}` and proves
`arcTime_mem_Icc : arcTime A γ r ∈ Icc 0 1` and **CORE** (`fwdHull_eq_image_Ioc_arcTime`):
under the hypotheses

`hA : Continuous A`, `hγc : ContinuousOn γ (Icc 0 1)`, `hγi : InjOn γ (Icc 0 1)`,
`hK : fwdHull A T = γ '' Ioc 0 1`, `hr : 0 ≤ r`, `hrT : r ≤ T`

one has `fwdHull A r = γ '' Ioc 0 (arcTime A γ r)`.

## Main results (exact statements)

* `arcTime_mono` (**monotonicity in the time parameter**; no hypothesis on `A` or `γ`):
  `∀ {s r : ℝ}, s ≤ r → arcTime A γ s ≤ arcTime A γ r`.
* `arcTime_zero` (`hA : Continuous A`): `arcTime A γ 0 = 0`.
* `arcTime_eq_one_of_fwdHull_eq` (`hK : fwdHull A T = γ '' Ioc 0 1`): `arcTime A γ T = 1`.
* `fwdHull_eq_of_arcTime_eq` (CORE hypotheses, `r, r' ∈ Icc 0 T`):
  `arcTime A γ r = arcTime A γ r' → fwdHull A r = fwdHull A r'`.
* `strictMonoOn_arcTime` (`hA`, `A 0 = 0`, CORE hypotheses):
  `StrictMonoOn (arcTime A γ) (Icc 0 T)`.
* `monotoneOn_arcTime`: `MonotoneOn (arcTime A γ) (Icc 0 T)`.

## Hypotheses: what is needed and why

* `A 0 = 0` is genuinely needed in `strictMonoOn_arcTime`: it enters through
  `RS.fwdHull_ssubset`, i.e. strict growth of hulls, whose proof uses the time-reversal
  normalisation at `0` (`RS.fwdHull_nonempty_of_pos`, a Phragmén–Lindelöf argument). Without it
  the statement is not available from the library, and equal hulls at two times would not
  contradict the clock.
* `Continuous A` is needed in `arcTime_zero` only, for `RS.fwdHull_zero_eq_empty`
  (`swallowTime_pos` is proved for continuous drivers); `fwdHull A 0 = ∅` is false in general.
* Nothing below uses `0 < T`: (1) and (2) only evaluate at the endpoints of `Icc 0 T`, and
  (3) only uses `0 ≤ r ≤ T`. We therefore do not assume it.
* `hγc`, `hγi` are only needed where CORE (`fwdHull_eq_image_Ioc_arcTime`) is used; the
  injectivity is what lets us read off the hull equality from the parameter equality.

## Proofs

(4) `K_s = fwdHull A s ⊆ fwdHull A r = K_r` for `s ≤ r` (`fwdHull_mono_coreArc`), so
`I_s ⊆ I_r` for the two defining sets; `csSup_le_csSup` gives `sSup I_s ≤ sSup I_r`, and if
`I_s = ∅` both sides are `0` (`arcTime_mem_Icc`, `Real.sSup_empty`).
(1) `K_0 = ∅` (`RS.fwdHull_zero_eq_empty`), so `I_0 = ∅` and `sSup ∅ = 0`.
(2) `fwdHull A T = γ '' Ioc 0 1` says `γ u ∈ K_T` for every `u ∈ Ioc 0 1`, so `I_T = Ioc 0 1`
and `sSup (Ioc 0 1) = 1` (`csSup_le`, `le_csSup`).
(3) `arcTime` is monotone by (4). If `arcTime A γ r = arcTime A γ r'` for `r < r'` with
`r, r' ∈ Icc 0 T`, CORE gives
`K_r = γ '' Ioc 0 (arcTime A γ r) = γ '' Ioc 0 (arcTime A γ r') = K_{r'}`, so `K_{r'} ⊆ K_r`,
contradicting the second component of `RS.fwdHull_ssubset hA hA0 hr.1 hrr' : K_r ⊂ K_{r'}`
(which, by `Set.ssubset_def`, is `¬ K_{r'} ⊆ K_r`).

## Sources

Route of `blueprint/CORE_ARC_PLAN.md` (the project's own; no published proof of this direction
was found — see `handoff/CORE-2.md`). The statements and their proofs are elementary
consequences of the two imports; "own elementary proof" applies to each item (the only
substantial ingredient, `RS.fwdHull_ssubset`, is itself proved in `HullBasics.lean`).
-/

noncomputable section

open Set Filter Topology Metric

namespace QuantumZipper

namespace CoreArc

variable {A : ℝ → ℝ} {T : ℝ} {γ : ℝ → ℂ}

/-- **(4) Monotonicity of the tip parameter.** `arcTime A γ` is monotone in the time
parameter. No hypothesis on `A` or `γ`. -/
theorem arcTime_mono {s r : ℝ} (hsr : s ≤ r) : arcTime A γ s ≤ arcTime A γ r := by
  set I := {u ∈ Ioc (0 : ℝ) 1 | γ u ∈ fwdHull A s} with hI
  set J := {u ∈ Ioc (0 : ℝ) 1 | γ u ∈ fwdHull A r} with hJ
  have hsub : I ⊆ J := fun u hu => ⟨hu.1, fwdHull_mono_coreArc hsr hu.2⟩
  rcases I.eq_empty_or_nonempty with hemp | hne
  · have h0 : arcTime A γ s = 0 := by
      rw [show arcTime A γ s = sSup I from rfl, hemp, Real.sSup_empty]
    rw [h0]
    exact (arcTime_mem_Icc (A := A) (γ := γ) (r := r)).1
  · exact csSup_le_csSup ⟨1, fun x hx => hx.1.2⟩ hne hsub

/-- **(1)** At time `0` the hull is empty, so the tip parameter is `0`. -/
theorem arcTime_zero (hA : Continuous A) : arcTime A γ 0 = 0 := by
  have hemp : {u ∈ Ioc (0 : ℝ) 1 | γ u ∈ fwdHull A 0} = ∅ := by
    rw [RS.fwdHull_zero_eq_empty hA]
    exact eq_empty_of_forall_notMem fun u hu => hu.2
  rw [show arcTime A γ 0 = sSup {u ∈ Ioc (0 : ℝ) 1 | γ u ∈ fwdHull A 0} from rfl, hemp,
    Real.sSup_empty]

/-- **(2)** If the hull at time `T` is the whole arc, the tip parameter at `T` is `1`. -/
theorem arcTime_eq_one_of_fwdHull_eq (hK : fwdHull A T = γ '' Ioc (0 : ℝ) 1) :
    arcTime A γ T = 1 := by
  have hI : {u ∈ Ioc (0 : ℝ) 1 | γ u ∈ fwdHull A T} = Ioc (0 : ℝ) 1 := by
    ext u
    exact ⟨fun h => h.1, fun hu => ⟨hu, by rw [hK]; exact ⟨u, hu, rfl⟩⟩⟩
  have hone : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hhalf : (1 / 2 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hsup : sSup (Ioc (0 : ℝ) 1) = 1 :=
    le_antisymm (csSup_le ⟨1 / 2, hhalf⟩ fun x hx => hx.2)
      (le_csSup ⟨1, fun x hx => hx.2⟩ hone)
  rw [show arcTime A γ T = sSup {u ∈ Ioc (0 : ℝ) 1 | γ u ∈ fwdHull A T} from rfl, hI, hsup]

/-- **CORE, injectivity of the tip parameter.** Under the CORE hypotheses, equal tip parameters
(at times in `Icc 0 T`) give equal hulls. -/
theorem fwdHull_eq_of_arcTime_eq {r r' : ℝ} (hA : Continuous A)
    (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hK : fwdHull A T = γ '' Ioc (0 : ℝ) 1) (hr : r ∈ Icc 0 T) (hr' : r' ∈ Icc 0 T)
    (heq : arcTime A γ r = arcTime A γ r') : fwdHull A r = fwdHull A r' := by
  rw [fwdHull_eq_image_Ioc_arcTime hA hγc hγi hK hr.1 hr.2,
    fwdHull_eq_image_Ioc_arcTime hA hγc hγi hK hr'.1 hr'.2, heq]

/-- **(3) Strict monotonicity.** Under the CORE hypotheses (with `A 0 = 0`), the tip parameter
is strictly increasing on `[0,T]`. -/
theorem strictMonoOn_arcTime (hA : Continuous A) (hA0 : A 0 = 0)
    (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hK : fwdHull A T = γ '' Ioc (0 : ℝ) 1) : StrictMonoOn (arcTime A γ) (Icc 0 T) := by
  intro r hr r' hr' hrr'
  refine lt_of_le_of_ne (arcTime_mono hrr'.le) fun heq => ?_
  have heqH : fwdHull A r = fwdHull A r' := fwdHull_eq_of_arcTime_eq hA hγc hγi hK hr hr' heq
  -- `K_{r'} = K_r`, so `K_{r'} ⊆ K_r`, contradicting `K_r ⊂ K_{r'}` (i.e. `¬ K_{r'} ⊆ K_r`)
  have hle : fwdHull A r' ⊆ fwdHull A r := by
    intro x hx
    simpa [heqH] using hx
  exact (RS.fwdHull_ssubset hA hA0 hr.1 hrr').2 hle

end CoreArc

end QuantumZipper
