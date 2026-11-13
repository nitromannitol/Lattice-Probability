/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cM.Cond at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.BridgeClock
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.Translate
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.JointMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cM.PushArea

/-!
# Borel conditions on a curve and a time change that give the bridge hypotheses

Source: [18], §1.2 and Lemma 4.3.

For a Lebesgue-time curve `c : C(ℝ, ℂ)` and a time change `ψ : C(ℝ, ℝ)`, `L43MCond c ψ` says: `ψ` is a
strictly increasing bijection, `c` is transient with dense range, and `c ∘ ψ` is parametrized by the
push-forward of Lebesgue measure under `c ∘ ψ`. Then (`L43MCond.bridgeHyp`) the `BridgeHyp` holds for the
measure `volume.map (c ∘ ψ)` on every bounded open set, so the local good event of `(volume.map (c ∘ ψ))|_V`
and `c` is the geometric good event of `c ∘ ψ`.

`measurableSet_l43mCond`: the set of pairs `(c, ψ)` satisfying `L43MCond` is **Borel** in
`C(ℝ, ℂ) × C(ℝ, ℝ)` (every condition reduces to countably many rational times).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4cM

open MatedCRTHarmonic

/-- **Conditions on a Lebesgue-time curve and a time change** under which `c ∘ ψ` is parametrized by the
push-forward of Lebesgue measure. -/
structure L43MCond (c : C(ℝ, ℂ)) (ψ : C(ℝ, ℝ)) : Prop where
  mono : StrictMono ψ
  surj : Function.Surjective ψ
  transient : Tendsto c (cocompact ℝ) (cocompact ℂ)
  dense : DenseRange c
  area : ∀ s t : ℝ, s ≤ t →
    volume.map (c.comp ψ) ((c.comp ψ) '' Icc s t) = ENNReal.ofReal (t - s)

namespace L43MCond

variable {c : C(ℝ, ℂ)} {ψ : C(ℝ, ℝ)}
/-- The time change as an order isomorphism. -/
def orderIso (h : L43MCond c ψ) : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective ψ h.mono h.surj

/-- A transient curve with dense range is surjective. -/
theorem surjective (h : L43MCond c ψ) : Function.Surjective c := by
  have hp : IsProperMap c := isProperMap_iff_tendsto_cocompact.2 ⟨c.continuous, h.transient⟩
  intro w
  have hw : w ∈ closure (range c) := by
    rw [h.dense.closure_range]
    exact mem_univ w
  rw [hp.isClosed_range.closure_eq] at hw
  exact hw

/-- **the bridge hypotheses** for the push-forward of Lebesgue measure under `c ∘ ψ`. -/
theorem bridgeHyp (h : L43MCond c ψ) {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V) :
    GMS4FO.BridgeHyp (volume.map (c.comp ψ)) c h.orderIso V where
  cont := c.continuous
  area := h.area
  visits := GMS4FO.hasFirstVisits_of_surjective h.surjective h.transient
  transient := h.transient
  isOpen := hV
  bounded := hVb

end L43MCond

/-! ### Reduction to rational times -/

/-- A closed condition holding at every rational time holds at every real time. -/
theorem forall_real_of_forall_rat {p : ℝ → Prop} (hp : IsClosed {t | p t}) (h : ∀ q : ℚ, p q)
    (t : ℝ) : p t := by
  have hsub : range ((↑) : ℚ → ℝ) ⊆ {t | p t} := by
    rintro _ ⟨q, rfl⟩
    exact h q
  have := hp.closure_subset_iff.2 hsub
  rw [Rat.denseRange_cast.closure_range] at this
  exact this (mem_univ t)

theorem strictMono_iff_rat (ψ : C(ℝ, ℝ)) :
    StrictMono ψ ↔ ∀ q q' : ℚ, q < q' → ψ q < ψ q' := by
  refine ⟨fun h q q' hqq' => h (by exact_mod_cast hqq'), fun h s t hst => ?_⟩
  -- `ψ s ≤ ψ q` for every rational `q > s`
  have hle : ∀ (s : ℝ) (q : ℚ), s < q → ψ s ≤ ψ q := by
    intro s q hsq
    by_contra hlt
    rw [not_le] at hlt
    have hev : ∀ᶠ x in 𝓝 s, ψ q < ψ x := (ψ.continuous.tendsto s).eventually (lt_mem_nhds hlt)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (lt_min (by linarith : s < s + δ) hsq)
    have hrq : (r : ℝ) < q := lt_of_lt_of_le hr2 (min_le_right _ _)
    have hrs : dist (r : ℝ) s < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      have := lt_of_lt_of_le hr2 (min_le_left _ _)
      linarith
    have h1 := hball hrs
    have h2 := h r q (by exact_mod_cast hrq)
    linarith
  have hge : ∀ (t : ℝ) (q : ℚ), (q : ℝ) < t → ψ q ≤ ψ t := by
    intro t q hqt
    by_contra hlt
    rw [not_le] at hlt
    have hev : ∀ᶠ x in 𝓝 t, ψ x < ψ q := (ψ.continuous.tendsto t).eventually (gt_mem_nhds hlt)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (max_lt hqt (by linarith : t - δ < t))
    have hqr : (q : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hr1
    have hrt : dist (r : ℝ) t < δ := by
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      have := lt_of_le_of_lt (le_max_right _ _) hr1
      linarith
    have h1 := hball hrt
    have h2 := h q r (by exact_mod_cast hqr)
    linarith
  obtain ⟨q, hsq, hqt⟩ := exists_rat_btwn hst
  obtain ⟨q', hqq', hq't⟩ := exists_rat_btwn hqt
  have h1 := hle s q hsq
  have h2 := h q q' (by exact_mod_cast hqq')
  have h3 := hge t q' hq't
  linarith

theorem surjective_iff_of_strictMono {ψ : C(ℝ, ℝ)} (hψ : StrictMono ψ) :
    Function.Surjective ψ ↔ ∀ n : ℕ, ∃ m : ℕ, (n : ℝ) ≤ ψ m ∧ ψ (-(m : ℝ)) ≤ -(n : ℝ) := by
  constructor
  · intro hs n
    obtain ⟨u, hu⟩ := hs n
    obtain ⟨u', hu'⟩ := hs (-(n : ℝ))
    obtain ⟨m, hm⟩ := exists_nat_ge (max |u| |u'|)
    refine ⟨m, ?_, ?_⟩
    · rw [← hu]
      exact hψ.monotone (by linarith [le_abs_self u, le_max_left |u| |u'|])
    · rw [← hu']
      exact hψ.monotone (by linarith [neg_abs_le u', le_max_right |u| |u'|])
  · intro h w
    obtain ⟨n, hn⟩ := exists_nat_ge |w|
    obtain ⟨m, hm1, hm2⟩ := h n
    have hmem : w ∈ Icc (ψ (-(m : ℝ))) (ψ m) :=
      ⟨by linarith [neg_abs_le w], by linarith [le_abs_self w]⟩
    have hle : -(m : ℝ) ≤ m := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    obtain ⟨u, -, hu⟩ := intermediate_value_Icc hle ψ.continuous.continuousOn hmem
    exact ⟨u, hu⟩

theorem transient_iff_real (c : C(ℝ, ℂ)) :
    Tendsto c (cocompact ℝ) (cocompact ℂ) ↔
      ∀ n : ℕ, ∃ m : ℕ, ∀ t : ℝ, (m : ℝ) < |t| → (n : ℝ) ≤ ‖c t‖ := by
  rw [← Metric.cobounded_eq_cocompact, ← Metric.cobounded_eq_cocompact,
    (Metric.hasBasis_cobounded_compl_closedBall (0 : ℝ)).tendsto_iff
      (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ))]
  simp only [true_and, forall_const, mem_compl_iff, mem_closedBall, dist_zero_right, not_le,
    Real.norm_eq_abs]
  constructor
  · intro h n
    obtain ⟨r, hr⟩ := h n
    obtain ⟨m, hm⟩ := exists_nat_ge r
    exact ⟨m, fun t ht => (hr t (lt_of_le_of_lt hm ht)).le⟩
  · intro h R
    obtain ⟨n, hn⟩ := exists_nat_gt R
    obtain ⟨m, hm⟩ := h n
    exact ⟨m, fun t ht => lt_of_lt_of_le hn (hm t ht)⟩

theorem transient_iff_rat (c : C(ℝ, ℂ)) :
    Tendsto c (cocompact ℝ) (cocompact ℂ) ↔
      ∀ n : ℕ, ∃ m : ℕ, ∀ q : ℚ, (m : ℝ) < |(q : ℝ)| → (n : ℝ) ≤ ‖c q‖ := by
  rw [transient_iff_real]
  refine ⟨fun h n => ?_, fun h n => ?_⟩
  · obtain ⟨m, hm⟩ := h n
    exact ⟨m, fun q hq => hm q hq⟩
  · obtain ⟨m, hm⟩ := h n
    refine ⟨m, fun t ht => ?_⟩
    have hcl : IsClosed {t : ℝ | |t| ≤ m ∨ (n : ℝ) ≤ ‖c t‖} :=
      (isClosed_le continuous_abs continuous_const).union
        (isClosed_le continuous_const (continuous_norm.comp c.continuous))
    have := forall_real_of_forall_rat (p := fun t : ℝ => |t| ≤ m ∨ (n : ℝ) ≤ ‖c t‖) hcl
      (fun q => by
        by_cases hq : (m : ℝ) < |(q : ℝ)|
        · exact Or.inr (hm q hq)
        · exact Or.inl (not_lt.1 hq)) t
    rcases this with h1 | h1
    · exact absurd ht (not_lt.2 h1)
    · exact h1

theorem denseRange_iff_rat (c : C(ℝ, ℂ)) :
    DenseRange c ↔ ∀ i n : ℕ, ∃ q : ℚ,
      dist (c q) (TopologicalSpace.denseSeq ℂ i) < 1 / ((n : ℝ) + 1) := by
  constructor
  · intro h i n
    have hd : DenseRange (c ∘ ((↑) : ℚ → ℝ)) := h.comp Rat.denseRange_cast c.continuous
    obtain ⟨q, hq⟩ := Metric.denseRange_iff.1 hd (TopologicalSpace.denseSeq ℂ i)
      (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨q, by rw [dist_comm]; exact hq⟩
  · intro h
    have hd : DenseRange (c ∘ ((↑) : ℚ → ℝ)) := by
      refine Metric.denseRange_iff.2 fun x r hr => ?_
      obtain ⟨i, hi⟩ := Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq ℂ) x (r / 2)
        (by positivity)
      obtain ⟨n, hn⟩ := exists_nat_gt (2 / r)
      obtain ⟨q, hq⟩ := h i n
      refine ⟨q, ?_⟩
      have hn' : 1 / ((n : ℝ) + 1) < r / 2 := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hr] at hn
        nlinarith
      calc dist x ((c ∘ ((↑) : ℚ → ℝ)) q)
          ≤ dist x (TopologicalSpace.denseSeq ℂ i) + dist (TopologicalSpace.denseSeq ℂ i) (c q) :=
            dist_triangle _ _ _
        _ < r / 2 + r / 2 := by
            rw [dist_comm (TopologicalSpace.denseSeq ℂ i)]
            exact add_lt_add hi (hq.trans hn')
        _ = r := by ring
    exact hd.mono (range_comp_subset_range _ _)

/-- **The area condition at rational times implies it at all real times.** -/
theorem area_of_rat {m : Measure ℂ} {e : ℝ → ℂ}
    (h : ∀ q q' : ℚ, q < q' → m (e '' Icc (q : ℝ) q') = ENNReal.ofReal (q' - q)) {s t : ℝ}
    (hst : s ≤ t) : m (e '' Icc s t) = ENNReal.ofReal (t - s) := by
  have hup : ∀ δ : ℝ, 0 < δ → m (e '' Icc s t) ≤ ENNReal.ofReal (t - s) + ENNReal.ofReal (2 * δ) := by
    intro δ hδ
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (by linarith : s - δ < s)
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (by linarith : t < t + δ)
    have hab : a < b := by exact_mod_cast (by linarith : (a : ℝ) < b)
    calc m (e '' Icc s t) ≤ m (e '' Icc (a : ℝ) b) :=
          measure_mono (image_mono (Icc_subset_Icc ha2.le hb1.le))
      _ = ENNReal.ofReal (b - a) := h a b hab
      _ ≤ ENNReal.ofReal (t - s + 2 * δ) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal (t - s) + ENNReal.ofReal (2 * δ) :=
          ENNReal.ofReal_add (by linarith) (by linarith)
  have hle : m (e '' Icc s t) ≤ ENNReal.ofReal (t - s) := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have := hup (ε / 2) (by positivity)
    rwa [show 2 * ((ε : ℝ) / 2) = ε by ring, ENNReal.ofReal_coe_nnreal] at this
  refine le_antisymm hle ?_
  rcases hst.eq_or_lt with heq | hlt
  · subst heq
    simp
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set δ : ℝ := min ((ε : ℝ) / 2) ((t - s) / 3) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by linarith)
  have hδ1 : δ ≤ (ε : ℝ) / 2 := min_le_left _ _
  have hδ2 : δ ≤ (t - s) / 3 := min_le_right _ _
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (by linarith : s < s + δ)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (by linarith : t - δ < t)
  have hab : a < b := by exact_mod_cast (by linarith : (a : ℝ) < b)
  calc ENNReal.ofReal (t - s) ≤ ENNReal.ofReal ((b - a : ℝ) + ε) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal (b - a) + ε := by
        rw [ENNReal.ofReal_add (by linarith) (by positivity), ENNReal.ofReal_coe_nnreal]
    _ = m (e '' Icc (a : ℝ) b) + ε := by rw [h a b hab]
    _ ≤ m (e '' Icc s t) + ε :=
        add_le_add (measure_mono (image_mono (Icc_subset_Icc ha1.le hb2.le))) le_rfl

theorem area_iff_rat {m : Measure ℂ} {e : ℝ → ℂ} :
    (∀ s t : ℝ, s ≤ t → m (e '' Icc s t) = ENNReal.ofReal (t - s)) ↔
      ∀ q q' : ℚ, q < q' → m (e '' Icc (q : ℝ) q') = ENNReal.ofReal (q' - q) :=
  ⟨fun h q q' hqq' => h q q' (by exact_mod_cast hqq'.le), fun h _ _ hst => area_of_rat h hst⟩

/-! ### Measurability -/

theorem measurable_comp_pair : Measurable fun x : C(ℝ, ℂ) × C(ℝ, ℝ) => x.1.comp x.2 :=
  (ContinuousMap.continuous_comp'.comp continuous_swap).measurable

/-- `e ↦ (e_* Leb)(e([a, b]))` is Borel. -/
theorem measurable_pushArea_image (a b : ℝ) :
    Measurable fun e : C(ℝ, ℂ) => volume.map e (e '' Icc a b) := by
  have hS : MeasurableSet {p : C(ℝ, ℂ) × ℝ | ∃ v ∈ Icc a b, p.1 v = p.1 p.2} := by
    have hc : Continuous fun p : C(ℝ, ℂ) × ℝ => (p.1, p.1 p.2) :=
      continuous_fst.prodMk continuous_eval
    exact ((GMS4b.isClosed_hitIn isCompact_Icc).preimage hc).measurableSet
  have heq : (fun e : C(ℝ, ℂ) => volume.map e (e '' Icc a b)) =
      fun e => volume (Prod.mk e ⁻¹' {p : C(ℝ, ℂ) × ℝ | ∃ v ∈ Icc a b, p.1 v = p.1 p.2}) := by
    funext e
    rw [Measure.map_apply e.continuous.measurable
      ((isCompact_Icc.image e.continuous).isClosed.measurableSet)]
    rfl
  rw [heq]
  exact measurable_measure_prodMk_left hS

theorem l43mCond_iff (c : C(ℝ, ℂ)) (ψ : C(ℝ, ℝ)) :
    L43MCond c ψ ↔
      (∀ q q' : ℚ, q < q' → ψ q < ψ q') ∧
      (∀ n : ℕ, ∃ m : ℕ, (n : ℝ) ≤ ψ m ∧ ψ (-(m : ℝ)) ≤ -(n : ℝ)) ∧
      (∀ n : ℕ, ∃ m : ℕ, ∀ q : ℚ, (m : ℝ) < |(q : ℝ)| → (n : ℝ) ≤ ‖c q‖) ∧
      (∀ i n : ℕ, ∃ q : ℚ, dist (c q) (TopologicalSpace.denseSeq ℂ i) < 1 / ((n : ℝ) + 1)) ∧
      (∀ q q' : ℚ, q < q' →
        volume.map (c.comp ψ) ((c.comp ψ) '' Icc (q : ℝ) q') = ENNReal.ofReal (q' - q)) := by
  constructor
  · intro h
    exact ⟨(strictMono_iff_rat ψ).1 h.mono, (surjective_iff_of_strictMono h.mono).1 h.surj,
      (transient_iff_rat c).1 h.transient, (denseRange_iff_rat c).1 h.dense, area_iff_rat.1 h.area⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have hmono := (strictMono_iff_rat ψ).2 h1
    exact ⟨hmono, (surjective_iff_of_strictMono hmono).2 h2, (transient_iff_rat c).2 h3,
      (denseRange_iff_rat c).2 h4, area_iff_rat.2 h5⟩

/-- **`L43MCond` is a Borel condition on `(c, ψ)`.** -/
theorem measurableSet_l43mCond :
    MeasurableSet {x : C(ℝ, ℂ) × C(ℝ, ℝ) | L43MCond x.1 x.2} := by
  have ev2 : ∀ t : ℝ, Measurable fun x : C(ℝ, ℂ) × C(ℝ, ℝ) => x.2 t := fun t =>
    (ContinuousMap.measurable_eval t).comp measurable_snd
  have ev1 : ∀ t : ℝ, Measurable fun x : C(ℝ, ℂ) × C(ℝ, ℝ) => x.1 t := fun t =>
    (ContinuousMap.measurable_eval t).comp measurable_fst
  simp_rw [l43mCond_iff]
  simp only [ofPred_and, ofPred_forall, ofPred_exists]
  refine (MeasurableSet.iInter fun (q : ℚ) => MeasurableSet.iInter fun (q' : ℚ) => ?_).inter
    ((MeasurableSet.iInter fun (n : ℕ) => MeasurableSet.iUnion fun (m : ℕ) => ?_).inter
    ((MeasurableSet.iInter fun (n : ℕ) => MeasurableSet.iUnion fun (m : ℕ) =>
      MeasurableSet.iInter fun (q : ℚ) => ?_).inter
    ((MeasurableSet.iInter fun (i : ℕ) => MeasurableSet.iInter fun (n : ℕ) =>
      MeasurableSet.iUnion fun (q : ℚ) => ?_).inter
    (MeasurableSet.iInter fun (q : ℚ) => MeasurableSet.iInter fun (q' : ℚ) => ?_))))
  · exact MeasurableSet.iInter fun _ => measurableSet_lt (ev2 _) (ev2 _)
  · exact (measurableSet_le measurable_const (ev2 _)).inter (measurableSet_le (ev2 _) measurable_const)
  · exact MeasurableSet.iInter fun _ => measurableSet_le measurable_const ((ev1 _).norm)
  · exact measurableSet_lt ((ev1 _).dist measurable_const) measurable_const
  · refine MeasurableSet.iInter fun _ => ?_
    have hm : Measurable fun x : C(ℝ, ℂ) × C(ℝ, ℝ) =>
        volume.map (x.1.comp x.2) ((x.1.comp x.2) '' Icc (q : ℝ) q') :=
      (measurable_pushArea_image _ _).comp measurable_comp_pair
    exact measurableSet_eq_fun hm measurable_const

end MatedCRTHarmonic.GMS4cM
