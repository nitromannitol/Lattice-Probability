/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3TrInv4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3TrInv3
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Sc2

/-!
# Translation invariance in law of `μ_{ĥ^tr}`, `μ_ĥ` and of their LGD events (P2-DGTRINV, part 4)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, DG:1243 (proof of Lemma 3.11):
"For each `S ∈ 𝒮(ℛ_n)`, the re-centered field `ĥ^tr(· − v_S + v_𝕊)` agrees in law with
`ĥ^tr`. By Lemma 3.12, it therefore follows that … `P[E_S^ε] = P[E_𝕊^ε] ≥ 1 − p`"; DG:953
("its law is still invariant with respect to rotations, translations, and reflections").

In the formalization the grid squares are carried to a fixed unit-frame square by the affine
maps of (3.7) together with the white noise `W ∘ U_{δ,c}` (`wnScale`, S3D105Sc1;
`ae_goodSq_scale`, S3L11Scale). The law statement needed for the union bounds is therefore:
**every LGD event of `μ_{ĥ^tr}` (or `μ_ĥ`) on a fixed box has the same probability for every white
noise**, in particular for all the rescaled/translated noises `W ∘ U_{δ,c}`:

* `dgLGDSetRat`, `dgLGDSet_eq_dgLGDSetRat`, `measurable_dgLGDSetRat`: the set-to-set distance
  `dgLGDSet` (DG's `D^ε(A, B; U)`) is a measurable function of the rational ball masses;
* **`prob_muTr_eq`**, **`prob_muHat_eq`**: `P[ballMassQ(μ_{ĥ^tr}[W]) ∈ S] = P'[ballMassQ(μ_{ĥ^tr}[W']) ∈ S]`;
* **`prob_goodSq_muTr_eq`**, **`prob_goodSq_muHat_eq`**: DG's `P[E_S^ε]` (`goodSq`, DG:1240)
  does not depend on the white noise; **`prob_goodSq_muTr_wnScaleDy`** (and `muHat`): the form
  for `W ∘ U_{2^{-j}, c}`, uniformly in `j, c` (DG (eqn-perc-prob));
* **`prob_dgLGDSet_muTr_eq`**: the same for the set-to-set events of DG L3.19/L3.13;
* **`dgTr_translate`**, **`map_dgTr_translate`**: the translation invariance in law of the
  circle-average process of `ĥ^tr` itself (DG:953), from `dgTr_wnScale` at `δ = 1`.

Own elementary glue; proposed DEVIATIONS entry in handoff/P2-DGTRINV.md.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3 SupTail QuantumZipper

/-! ### The set-to-set distance as a function of rational ball masses -/

/-- `N` rational balls are admissible for `D^ε(A, B; U)` -/
def dgRatAdmSet (m : ℚ × ℚ → ℚ → ℝ≥0∞) (ε : ℝ) (U A B : Set ℂ) (N : ℕ) : Prop :=
  ∃ (c : Fin N → ℚ × ℚ) (q : Fin N → ℚ),
    (∃ z ∈ A, ∃ w ∈ B, ∃ P : Path z w, ∀ t, ∃ i, P t ∈ Metric.ball (ratPt (c i)) (q i)) ∧
    ∀ i, (0 < q i ∧ Metric.ball (ratPt (c i)) (q i) ⊆ closure U) ∧
      m (c i) (q i) ≤ ENNReal.ofReal ε

/-- `D^ε(A, B; U)` as a function of the rational ball masses -/
def dgLGDSetRat (m : ℚ × ℚ → ℚ → ℝ≥0∞) (ε : ℝ) (U A B : Set ℂ) : ℕ∞ :=
  ⨅ (N : ℕ) (_ : dgRatAdmSet m ε U A B N), (N : ℕ∞)

theorem dgLGDSet_eq_dgLGDSetRat (μ : Measure ℂ) (ε : ℝ) (U A B : Set ℂ) :
    dgLGDSet μ ε U A B = dgLGDSetRat (ballMassQ μ) ε U A B := by
  refine le_antisymm ?_ ?_
  · refine le_iInf₂ fun N hN => ?_
    obtain ⟨c, q, ⟨z, hz, w, hw, P, hP⟩, hm⟩ := hN
    refine (dgLGDSet_le hz hw).trans ?_
    rw [dgLGD_eq_dgLGDRat]
    exact iInf₂_le N ⟨c, q, ⟨P, hP⟩, hm⟩
  · refine le_iInf₂ fun z hz => le_iInf₂ fun w hw => ?_
    rw [dgLGD_eq_dgLGDRat]
    refine le_iInf₂ fun N hN => ?_
    obtain ⟨c, q, ⟨P, hP⟩, hm⟩ := hN
    exact iInf₂_le N ⟨c, q, ⟨z, hz, w, hw, P, hP⟩, hm⟩

lemma dgLGDSetRat_le_iff (m : ℚ × ℚ → ℚ → ℝ≥0∞) (ε : ℝ) (U A B : Set ℂ) (K : ℕ) :
    dgLGDSetRat m ε U A B ≤ K ↔ ∃ N, dgRatAdmSet m ε U A B N ∧ N ≤ K := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have : ((K + 1 : ℕ) : ℕ∞) ≤ dgLGDSetRat m ε U A B :=
      le_iInf₂ fun N hN => by exact_mod_cast hne N hN
    have := this.trans h
    norm_cast at this
    omega
  · rintro ⟨N, hN, hNK⟩
    exact (iInf₂_le N hN).trans (by exact_mod_cast hNK)

/-- **measurability of `dgLGDSetRat`** in the ball masses -/
theorem measurable_dgLGDSetRat (ε : ℝ) (U A B : Set ℂ) :
    Measurable fun m : ℚ × ℚ → ℚ → ℝ≥0∞ => dgLGDSetRat m ε U A B := by
  refine measurable_enat_of_le fun K => ?_
  simp_rw [dgLGDSetRat_le_iff, dgRatAdmSet]
  refine measurableSet_setOfPred.2 (Measurable.exists fun N => Measurable.and
    (Measurable.exists fun c => Measurable.exists fun q => Measurable.and measurable_const
      (Measurable.forall fun i => Measurable.and measurable_const
        (measurableSet_setOfPred.1 (measurableSet_le
          ((measurable_pi_apply _).comp (measurable_pi_apply _)) measurable_const))))
    measurable_const)

/-! ### `μ_{ĥ^tr}` and `μ_ĥ`: probabilities do not depend on the white noise -/

lemma interior_ferniqueBox_nonempty (y : ℂ) {b : ℝ} (hb : 0 < b) :
    (interior (ferniqueBox y b)).Nonempty := by
  refine ⟨⟨y.re + b / 2, y.im + b / 2⟩, ?_⟩
  unfold ferniqueBox
  rw [Complex.interior_reProdIm, interior_Icc, interior_Icc]
  exact ⟨⟨by simp; linarith, by simp; linarith⟩, ⟨by simp; linarith, by simp; linarith⟩⟩

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {W : WNSpace → Ω → ℝ} {W' : WNSpace → Ω' → ℝ}

/-- **the law of `μ_{ĥ^tr}` on `K` does not depend on the white noise** (DG:953, 1243) -/
theorem prob_muTr_eq (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare)
    {S : Set (ℚ × ℚ → ℚ → ℝ≥0∞)} (hS : MeasurableSet S) :
    P {ω | ballMassQ (muTr hW γ hb hK ω) ∈ S} = P' {ω | ballMassQ (muTr hW' γ hb hK ω) ∈ S} :=
  prob_muOfMod_eq hW hW' hγ hγ2 (isCompact_ferniqueBox y b) (ferniqueBox_subset hK)
    (volume_frontier_ferniqueBox y b) (interior_ferniqueBox_nonempty y hb)
    (Φ := fun z r w => Real.sqrt Real.pi * w (measKerL2 openSquare (Ioi 0) (circleUnif z r)) -
      Real.sqrt Real.pi * w (trMeasKerL2 (circleUnif z r)))
    (fun _ _ => ((measurable_pi_apply _).const_mul _).sub ((measurable_pi_apply _).const_mul _))
    (trMod_spec hW hb hK) (trMod_spec hW' hb hK) hS

/-! ### The rescaled and translated noises (DG:1243, (eqn-perc-prob)) -/

end DG
end LQGMetric
