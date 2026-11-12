/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.BilipLocal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.Defs
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw
import LatticeProb.Bonanno.LQGMetric.Prob.CondIndepDetermined
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.LQGMetric.Metric.Internal

/-!
# GM S2.3: weak LQG metrics are jointly local and ξ-additive (task P2-M2A, row 2)

GM (arXiv:1905.00383v3, `uniqueness-final.tex`) l. 905–914: "the metrics `D_h` and `D̃_h` are each
local for `h` due to Axiom II. Since these metrics are each determined by `h`, they are
conditionally independent given `h`. Therefore, we can apply [LM, Lemma 1.4] to get that `D_h` and
`D̃_h` are jointly local for `h`." and "By Axiom III (Weyl scaling), it follows that our metrics
`D_h` and `D̃_h` are [ξ-additive] for `h`" (GM writes "jointly local" for "ξ-additive", a typo,
`blueprint/GM_A.md` GM.S2.3).

* `Bilip.aeClosure μ G`: the σ-algebra of events a.s. equal to an event of `G`;
  `Bilip.condIndepEv_of_le_aeClosure`: if `A` is a.s. determined by `G`, then `A ⊥ B | G` for every
  `B` (elementary: pull-out property of conditional expectation);
  `Bilip.CondIndepEv.of_le_aeClosure`: conditional independence only depends on the σ-algebras up
  to null events.
* `Bilip.isLocalMetric_comp`: a weak LQG metric `D_h` is local for every whole-plane GFF `h`
  (LM Def 1.2) — Axiom II; LM's remark (LM l. 233: "if `D` is determined by `h`, local ⟺
  `D(·,·;V)` determined by `h|_V`"), the direction used here, is the lemma above.
* `gm_S2_3`: `(D_h, D̃_h)` are jointly local and ξ-additive for `h` (`IsXiAdditive2`), from
  `Blueprint.LMLem1_4` (LM Lemma 1.4) applied to `h` and to `h − h_r(z)`, and Weyl scaling with the
  constant `−h_r(z)` (`IsWeakLQGMetric.ae_internal_addFun_of_eq_const`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

namespace Bilip

section AEClosure

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- the σ-algebra of the sets that are a.s. equal to a set of `G` -/
def aeClosure (μ : Measure[mΩ] Ω) (G : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' s := ∃ t, MeasurableSet[G] t ∧ s =ᵐ[μ] t
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ G, EventuallyEq.rfl⟩
  measurableSet_compl s := fun ⟨t, ht, hst⟩ => ⟨tᶜ, ht.compl, hst.compl⟩
  measurableSet_iUnion f hf := by
    choose t ht hft using hf
    exact ⟨⋃ i, t i, MeasurableSet.iUnion ht, EventuallyEqSet.countable_iUnion hft⟩

lemma le_aeClosure (G : MeasurableSpace Ω) : G ≤ aeClosure μ G :=
  fun s hs => ⟨s, hs, EventuallyEq.rfl⟩

lemma aeClosure_mono {G G' : MeasurableSpace Ω} (h : G ≤ G') : aeClosure μ G ≤ aeClosure μ G' :=
  fun _ ⟨t, ht, hst⟩ => ⟨t, h t ht, hst⟩

lemma aeClosure_aeClosure_le (G : MeasurableSpace Ω) :
    aeClosure μ (aeClosure μ G) ≤ aeClosure μ G :=
  fun _ ⟨_, ⟨t', ht', htt'⟩, hst⟩ => ⟨t', ht', hst.trans htt'⟩

/-- If `A` is a.s. determined by `G` (and the events of `B` are a.s. equal to measurable events),
then `A` and `B` are conditionally independent given `G`. -/
theorem condIndepEv_of_le_aeClosure [IsFiniteMeasure μ] {G A B : MeasurableSpace Ω}
    (hG : G ≤ mΩ) (hA : A ≤ aeClosure μ G) (hB : B ≤ aeClosure μ mΩ) : CondIndepEv G A B μ := by
  intro a b ha hb
  obtain ⟨a', ha', haa⟩ := hA a ha
  obtain ⟨b', hb', hbb⟩ := hB b hb
  have e1 : μ⟦a ∩ b | G⟧ =ᵐ[μ] μ⟦a' ∩ b' | G⟧ :=
    condExp_congr_ae (indOne_ae_eq_of_ae_eq (haa.inter hbb))
  have e2 : μ⟦a | G⟧ =ᵐ[μ] μ⟦a' | G⟧ := condExp_congr_ae (indOne_ae_eq_of_ae_eq haa)
  have e3 : μ⟦b | G⟧ =ᵐ[μ] μ⟦b' | G⟧ := condExp_congr_ae (indOne_ae_eq_of_ae_eq hbb)
  have e4 : μ⟦a' | G⟧ = a'.indicator fun _ => (1 : ℝ) :=
    condExp_of_stronglyMeasurable hG (stronglyMeasurable_const.indicator ha')
      (integrable_indOne (hG _ ha'))
  have e5 : μ⟦a' ∩ b' | G⟧ =ᵐ[μ] a'.indicator (μ⟦b' | G⟧) := by
    rw [← indicator_indicator]
    exact condExp_indicator (integrable_indOne hb') ha'
  filter_upwards [e1, e2, e3, e5] with x h1 h2 h3 h5
  simp only [Pi.mul_apply]
  rw [h1, h5, h2, h3, e4]
  by_cases hx : x ∈ a' <;> simp [hx]

/-- Conditional independence is unchanged when the σ-algebras are changed by null events. -/
theorem CondIndepEv.of_le_aeClosure {G A B A' B' : MeasurableSpace Ω} (h : CondIndepEv G A B μ)
    (hA : A' ≤ aeClosure μ A) (hB : B' ≤ aeClosure μ B) : CondIndepEv G A' B' μ := by
  intro a' b' ha' hb'
  obtain ⟨a, ha, haa⟩ := hA a' ha'
  obtain ⟨b, hb, hbb⟩ := hB b' hb'
  filter_upwards [h a b ha hb, condExp_congr_ae (m := G) (indOne_ae_eq_of_ae_eq (haa.inter hbb)),
    condExp_congr_ae (m := G) (indOne_ae_eq_of_ae_eq haa),
    condExp_congr_ae (m := G) (indOne_ae_eq_of_ae_eq hbb)] with x h0 h1 h2 h3
  simp only [Pi.mul_apply] at h0 ⊢
  rw [h1, h2, h3, h0]

end AEClosure

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

lemma famSigma_le_aeClosure_of_ae_eq {I J : Ω → Set ℂ → ℂ → ℂ → ℝ≥0∞} {V : Set ℂ}
    (h : ∀ᵐ ω ∂P, J ω V = I ω V) : famSigma J V ≤ aeClosure P (famSigma I V) := by
  rintro s ⟨S, hS, rfl⟩
  refine ⟨(fun ω => I ω V) ⁻¹' S, ⟨S, hS, rfl⟩, ?_⟩
  filter_upwards [h] with ω hω
  change (J ω V ∈ S) = (I ω V ∈ S)
  rw [hω]

lemma famSigma_le_aeClosure_of_measurable {I : Ω → Set ℂ → ℂ → ℂ → ℝ≥0∞} {V : Set ℂ}
    {G : MeasurableSpace Ω} {X : Ω → ℂ → ℂ → ℝ≥0∞} (hX : Measurable[G] X)
    (h : ∀ᵐ ω ∂P, I ω V = X ω) : famSigma I V ≤ aeClosure P G := by
  rintro s ⟨S, hS, rfl⟩
  refine ⟨X ⁻¹' S, hX hS, ?_⟩
  filter_upwards [h] with ω hω
  change (I ω V ∈ S) = (X ω ∈ S)
  rw [hω]

/-- Joint locality is unchanged when the families of internal metrics are changed, on open sets,
on a null event. -/
theorem isJointlyLocalFam_congr {h : Ω → DistC} {I₁ I₂ J₁ J₂ : Ω → Set ℂ → ℂ → ℂ → ℝ≥0∞}
    (hI : IsJointlyLocalFam P h I₁ I₂) (h₁ : ∀ᵐ ω ∂P, ∀ V : Set ℂ, IsOpen V → J₁ ω V = I₁ ω V)
    (h₂ : ∀ᵐ ω ∂P, ∀ V : Set ℂ, IsOpen V → J₂ ω V = I₂ ω V) : IsJointlyLocalFam P h J₁ J₂ := by
  intro V
  have hV := V.isOpen
  have hW : IsOpen (closure (V : Set ℂ))ᶜ := isClosed_closure.isOpen_compl
  have a1 : ∀ W : Set ℂ, IsOpen W → famSigma J₁ W ≤ aeClosure P (famSigma I₁ W) := fun W hW' =>
    famSigma_le_aeClosure_of_ae_eq (by filter_upwards [h₁] with ω hω using hω W hW')
  have a2 : ∀ W : Set ℂ, IsOpen W → famSigma J₂ W ≤ aeClosure P (famSigma I₂ W) := fun W hW' =>
    famSigma_le_aeClosure_of_ae_eq (by filter_upwards [h₂] with ω hω using hω W hW')
  refine CondIndepEv.of_le_aeClosure (hI V) (sup_le ?_ ?_) (sup_le (sup_le ?_ ?_) ?_)
  · exact (a1 _ hV).trans (aeClosure_mono le_sup_left)
  · exact (a2 _ hV).trans (aeClosure_mono le_sup_right)
  · exact (le_sup_left.trans le_sup_left).trans (le_aeClosure _)
  · exact (a1 _ hW).trans (aeClosure_mono (le_sup_right.trans le_sup_left))
  · exact (a2 _ hW).trans (aeClosure_mono le_sup_right)

lemma fieldSigma_le {h : Ω → DistC} (hh : Measurable h) (V : TopologicalSpace.Opens ℂ) :
    fieldSigma h V ≤ mΩ :=
  ((measurable_restrictTo V).comp hh).comap_le

lemma fieldSigmaClosed_le {h : Ω → DistC} (hh : Measurable h) (K : Set ℂ) :
    fieldSigmaClosed h K ≤ mΩ :=
  (iInf₂_le (1 : ℝ) one_pos).trans (fieldSigma_le hh _)

variable {γ : ℝ} {D D' : DistC → ContMetric} {c c' : ℝ → ℝ}

/-- Axiom II: the internal metric `D_h(·,·;V)` is a.s. determined by `h|_V`. -/
theorem famSigma_internal_le (hD : IsWeakLQGMetric γ D c) [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (V : TopologicalSpace.Opens ℂ) :
    famSigma (internalFam fun ω => D (h ω)) V ≤ aeClosure P (fieldSigma h V) := by
  obtain ⟨F, hF, hae⟩ := hD.locality P h (Tight.isGFFPlusCont_of_wp hh) V
  classical
  let G : DistOn V → ℂ → ℂ → ℝ≥0∞ := fun g z w => if z ∈ V ∧ w ∈ V then F g z w else ⊤
  have hG : Measurable G := measurable_pi_iff.2 fun z => measurable_pi_iff.2 fun w => by
    by_cases hzw : z ∈ V ∧ w ∈ V
    · have e : (fun g => G g z w) = fun g => F g z w := funext fun g => if_pos hzw
      rw [e]
      exact (measurable_pi_apply w).comp ((measurable_pi_apply z).comp hF)
    · have e : (fun g => G g z w) = fun _ => ⊤ := funext fun g => if_neg hzw
      rw [e]
      exact measurable_const
  refine famSigma_le_aeClosure_of_measurable
    (hG.comp (comap_measurable fun ω => restrictTo V (h ω))) ?_
  filter_upwards [hae] with ω hω
  funext z w
  change (D (h ω)).internal V z w = G (restrictTo V (h ω)) z w
  by_cases hzw : z ∈ V ∧ w ∈ V
  · rw [show G (restrictTo V (h ω)) z w = F (restrictTo V (h ω)) z w from if_pos hzw]
    exact hω z hzw.1 w hzw.2
  · rw [show G (restrictTo V (h ω)) z w = ⊤ from if_neg hzw]
    rcases not_and_or.1 hzw with hz | hw
    · refine MetricGeometry.internalEDist_eq_top_of_notMem_left ?_
      rintro ⟨x, hx, hxz⟩
      exact hz (by rw [← show x = z from hxz]; exact hx)
    · refine MetricGeometry.internalEDist_eq_top_of_notMem_right ?_
      rintro ⟨x, hx, hxw⟩
      exact hw (by rw [← show x = w from hxw]; exact hx)

/-- A weak LQG metric is a local metric (LM Def 1.2) for every whole-plane GFF (GM l. 905). -/
theorem isLocalMetric_comp (hD : IsWeakLQGMetric γ D c) [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) : IsLocalMetric P h fun ω => D (h ω) := by
  refine ⟨hD.measurable.comp hh.measurable, hD.length P h (Tight.isGFFPlusCont_of_wp hh),
    fun V => condIndepEv_of_le_aeClosure (fieldSigma_le hh.measurable V)
      (famSigma_internal_le hD hh V) (sup_le ?_ ?_)⟩
  · exact (fieldSigmaClosed_le hh.measurable _).trans (le_aeClosure _)
  · exact (famSigma_internal_le hD hh ⟨_, isClosed_closure.isOpen_compl⟩).trans
      (aeClosure_mono (fieldSigma_le hh.measurable _))

end Bilip

end LQGMetric.GM
