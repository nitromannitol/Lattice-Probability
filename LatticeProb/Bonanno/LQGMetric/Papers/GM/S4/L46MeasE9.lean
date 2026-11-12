/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasE9 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE7
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasD5
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEventRandom

/-!
# Null-measurability from analyticity on `lenSet`; hull events; the `arcOf` relation
(task P2-E3d, inputs `hnullE`, `hnullW`, `hnullGW` of `gm_L4_5_of_null'`)

GM = Gwynne–Miller, arXiv:1905.00383v3, Lemma 4.5 (l. 1655–1688). GM do not discuss
measurability; own descriptive-set-theory argument (D65).

* `gmE_nullMeas_of_an`: if `B` is analytic on `lenSet` and `D_h ∈ lenSet` a.s., then `D⁻¹(B)` is
  null-measurable for the law of `h` (Lusin: analytic sets are universally measurable);
* `gmE_meets_iff`, `gmE_hullAn`: `{d | (𝓑^•_{τ c}(𝕫; d))^{(n)} = S}` is Borel on `lenSet`
  (a dyadic square misses `𝓑^•` iff it avoids `cl 𝓑` and its centre is outside `𝓑^•`);
* `gm_arcOfRelAn`: the relation `y ∈ arcOf d 𝕫 t x` is analytic on `lenSet`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

/-- **analytic on `lenSet` ⇒ null-measurable for the law of the field** -/
theorem gmE_nullMeas_of_an {D : DistC → ContMetric} (hDm : Measurable D) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {h : Ω → DistC}
    (hm : AEMeasurable h P) (hL : ∀ᵐ ω ∂P, D (h ω) ∈ lenSet) {B : Set ContMetric} (hB : GMAnalyticOn lenSet B) :
    NullMeasurableSet (D ⁻¹' B) (P.map h) := by
  obtain ⟨β, m, sb, S, hS, hBS⟩ := hB
  have hU : UMeasurableSet (lenSet ∩ B) := by
    have e : lenSet ∩ B = {d | ∃ b, (d, b) ∈ S ∩ {q | q.1 ∈ lenSet}} := by
      ext d
      constructor
      · rintro ⟨hd, hb⟩
        obtain ⟨b, hb'⟩ := (hBS d hd).1 hb
        exact ⟨b, hb', hd⟩
      · rintro ⟨b, hb, hd⟩
        exact ⟨hd, (hBS d hd).2 ⟨b, hb⟩⟩
    rw [e]
    exact UMeasurableSet.setOf_exists (hS.inter (measurableSet_lenSet.preimage measurable_fst))
  have hn := (hU.preimage hDm).nullMeasurableSet (P.map h)
  refine hn.congr ?_
  have := (ae_map_iff hm (measurableSet_lenSet.preimage hDm)).2 hL
  filter_upwards [this] with g hg
  exact propext ⟨fun hb => hb.2, fun hb => ⟨hg, hb⟩⟩

/-! ## Hull events -/

lemma gmE_dyadicSq_eq (n : ℕ) (k : ℤ × ℤ) : dyadicSq n k =
    (Icc ((k.1 : ℝ) / 2 ^ n) ((k.1 + 1) / 2 ^ n)) ×ℂ (Icc ((k.2 : ℝ) / 2 ^ n) ((k.2 + 1) / 2 ^ n)) := by
  ext x; simp [dyadicSq, Complex.mem_reProdIm, and_assoc]

lemma gmE_isCompact_dyadicSq (n : ℕ) (k : ℤ × ℤ) : IsCompact (dyadicSq n k) := by
  rw [gmE_dyadicSq_eq]; exact isCompact_Icc.reProdIm isCompact_Icc

lemma gmE_isPreconnected_dyadicSq (n : ℕ) (k : ℤ × ℤ) : IsPreconnected (dyadicSq n k) := by
  rw [gmE_dyadicSq_eq]
  exact (((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)).isPreconnected

lemma gmE_subset_compl_filledBall_iff (d : ContMetric) (𝕫 : ℂ) (s : ℝ) {S : Set ℂ}
    (hS : IsPreconnected S) {c : ℂ} (hc : c ∈ S) :
    S ⊆ (filledBall d 𝕫 s)ᶜ ↔ S ⊆ (closure (ballM d 𝕫 s))ᶜ ∧ gmOutF d 𝕫 s c := by
  constructor
  · intro h
    exact ⟨fun v hv => ((gmE_notMem_filledBall_iff' d 𝕫 s v).1 (h hv)).1,
      (gmE_notMem_filledBall_iff d 𝕫 s c).1 (h hc)⟩
  · rintro ⟨hO, h2⟩
    have hcK := (gmE_notMem_filledBall_iff' d 𝕫 s c).1 ((gmE_notMem_filledBall_iff d 𝕫 s c).2 h2)
    have hsub := hS.subset_connectedComponentIn hc hO
    intro v hv
    refine (gmE_notMem_filledBall_iff' d 𝕫 s v).2 ⟨hO hv, ?_⟩
    rw [← connectedComponentIn_eq (hsub hv)]
    exact hcK.2

/-- "the square `dyadicSq n k` meets `𝓑^•_s(𝕫; d)`", countable form -/
def gmMeetsF (d : ContMetric) (𝕫 : ℂ) (s : ℝ) (n : ℕ) (k : ℤ × ℤ) : Prop :=
  ¬ ((∃ m : ℕ, ∀ i : ℕ, infDist (qd i) (dyadicSq n k) < 1 / ((m : ℝ) + 1) →
      s ≤ d.1 (𝕫, qd i)) ∧ gmOutF d 𝕫 s (sqCenter n k))

theorem gmE_meets_iff (d : ContMetric) (𝕫 : ℂ) (s : ℝ) (n : ℕ) (k : ℤ × ℤ) :
    (dyadicSq n k ∩ filledBall d 𝕫 s).Nonempty ↔ gmMeetsF d 𝕫 s n k := by
  have hc : sqCenter n k ∈ dyadicSq n k := (sqCenter_mem_iff n k k).2 rfl
  rw [gmMeetsF, ← gmE_subset_compl_closure_iff d 𝕫 s (gmE_isCompact_dyadicSq n k) ⟨_, hc⟩,
    ← gmE_subset_compl_filledBall_iff d 𝕫 s (gmE_isPreconnected_dyadicSq n k) hc,
    subset_compl_iff_disjoint_right,
    not_disjoint_iff_nonempty_inter]

lemma gmE_measurable_meetsF {X : Type} [MeasurableSpace X] {f : X → ContMetric} {s : X → ℝ}
    (hf : Measurable f) (hs : Measurable s) (𝕫 : ℂ) (n : ℕ) (k : ℤ × ℤ) :
    Measurable fun q => gmMeetsF (f q) 𝕫 (s q) n k :=
  ((Measurable.exists fun m => Measurable.forall fun i => measurable_const.imp
    (measurableSet_setOfPred.1 (measurableSet_le hs ((measurable_apply (𝕫, qd i)).comp hf)))).and
    (gmE_measurable_outF_comp hf hs measurable_const 𝕫)).not

/-- **hull events are Borel on `lenSet`** -/
theorem gmE_hullAn (𝕫 : ℂ) (R c : ℝ) (n : ℕ) (S : Set ℂ) :
    GMAnalyticOn lenSet {d | dyadicHull n (filledBall d 𝕫 (tauD d 𝕫 R * c)) = S} := by
  classical
  by_cases hS : ∃ B, dyadicHull n B = S
  · obtain ⟨B, rfl⟩ := hS
    have hm : Measurable fun d : ContMetric => gmTauB 𝕫 R d * c :=
      (gm_measurable_tauB 𝕫 R).mul_const c
    refine gmAn_congr (gmAn_of_measurableSet (A := {d | ∀ k, (gmMeetsF d 𝕫 (gmTauB 𝕫 R d * c) n k ↔
      (dyadicSq n k ∩ B).Nonempty)}) (measurableSet_setOfPred.2 (Measurable.forall fun k => ?_)))
      fun d hd => ?_
    · by_cases hp : (dyadicSq n k ∩ B).Nonempty
      · simpa only [hp, iff_true] using gmE_measurable_meetsF measurable_id' hm 𝕫 n k
      · simpa only [hp, iff_false] using (gmE_measurable_meetsF measurable_id' hm 𝕫 n k).not
    · simp only [mem_ofPred_eq, hull_eq_iff, gm_tauD_eq_tauB hd, gmE_meets_iff]
  · refine gmAn_congr (gmAn_of_measurableSet MeasurableSet.empty) fun d _ => ?_
    simp only [mem_empty_iff_false, mem_ofPred_eq, false_iff]
    exact fun h => hS ⟨_, h⟩

/-! ## The `arcOf` relation -/

end LQGMetric.GM
