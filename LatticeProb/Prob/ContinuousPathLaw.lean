import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLastZeroR

/-!
# Continuous paths, last zeros and entrance densities

General forms of path-space, last-zero and analytic-limit facts for a real
path `c : ℝ → ℝ` and for continuous paths `ℝ≥0 → ℝ`, with the Mathlib
continuous-map space `C(ℝ≥0, ℝ)` in place of a path type.

* Path space: a finite measure on `C(ℝ≥0, ℝ)` is determined by the law of its
  coordinate process, and an almost surely continuous measurable coordinate
  process has a measurable continuous-path version.
* Last zero: for a path `c` tending to `+∞`, the last zero `sup {s ≥ 0 : c s = 0}`
  is also the supremum of the rational levels at which the path is nonpositive
  at or after that level.
* Analytic limits: right-hand limits of quotients of functions vanishing at
  the origin, and the entrance-density limit of the killed drifted Brownian
  transition formula, for a centred Gaussian density of variance `t`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace LatticeProb.ContinuousPathLaw

/-- A quotient of functions vanishing at the origin has the quotient of
their nonzero first derivatives as its right-hand limit. -/
theorem tendsto_div_of_hasDerivAt_zero {f g : ℝ → ℝ} {a b : ℝ}
    (hf : HasDerivAt f a 0) (hg : HasDerivAt g b 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hb : b ≠ 0) :
    Tendsto (fun x => f x / g x) (𝓝[>] 0) (𝓝 (a / b)) := by
  have hf' := hf.tendsto_slope_zero_right
  have hg' := hg.tendsto_slope_zero_right
  simp only [zero_add, hf0, hg0, sub_zero, smul_eq_mul] at hf' hg'
  have h := hf'.div hg' hb
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ 0 := ne_of_gt hx
  dsimp
  field_simp

/-- The analytic entrance-density limit for the killed drifted Brownian
transition formula.  The hypothesis on `g` is the derivative identity for
the centered Gaussian density of variance `t`. -/
theorem tendsto_conditioned_entrance_density
    (g : ℝ → ℝ) (d t y : ℝ) (hd : d ≠ 0) (ht : t ≠ 0)
    (hg : HasDerivAt g (-(y / t) * g y) y) :
    Tendsto (fun x =>
      (Real.exp (d * (y - x) - d ^ 2 * t / 2) * (g (y - x) - g (y + x))) *
        (1 - Real.exp (-2 * d * y)) / (1 - Real.exp (-2 * d * x)))
      (𝓝[>] 0)
      (𝓝 ((y / (d * t)) * g y * Real.exp (d * y - d ^ 2 * t / 2) *
        (1 - Real.exp (-2 * d * y)))) := by
  have hminus : HasDerivAt (fun x => g (y - x)) (y / t * g y) 0 := by
    have hg' : HasDerivAt g (-(y / t) * g y) (y - 0) := by simpa using hg
    convert hg'.comp 0 ((hasDerivAt_const 0 y).sub (hasDerivAt_id 0)) using 1
    all_goals first | rfl | simp
  have hplus : HasDerivAt (fun x => g (y + x)) (-(y / t) * g y) 0 := by
    have hg' : HasDerivAt g (-(y / t) * g y) (y + 0) := by simpa using hg
    convert hg'.comp 0 ((hasDerivAt_const 0 y).add (hasDerivAt_id 0)) using 1
    all_goals first | rfl | simp
  have hnum : HasDerivAt (fun x => g (y - x) - g (y + x))
      (2 * (y / t * g y)) 0 := by
    convert hminus.sub hplus using 1; ring
  have hden : HasDerivAt (fun x => 1 - Real.exp (-2 * d * x)) (2 * d) 0 := by
    convert (hasDerivAt_const 0 (1 : ℝ)).sub
      (((hasDerivAt_const 0 (-2 * d)).mul (hasDerivAt_id 0)).exp) using 1 <;>
      simp [← Pi.sub_def]
  have hq := tendsto_div_of_hasDerivAt_zero hnum hden (by simp) (by simp) (by
    exact mul_ne_zero (by norm_num) hd)
  have he : Tendsto (fun x : ℝ => Real.exp (d * (y - x) - d ^ 2 * t / 2))
      (𝓝[>] 0) (𝓝 (Real.exp (d * y - d ^ 2 * t / 2))) := by
    have hc : Continuous (fun x : ℝ => Real.exp (d * (y - x) - d ^ 2 * t / 2)) := by
      fun_prop
    simpa using (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto _ (𝓝[>] (0 : ℝ)) _)
  have h := (he.mul hq).mul_const (1 - Real.exp (-2 * d * y))
  convert h using 1
  · ext x
    ring
  · congr 1
    field_simp

/-- Mathlib's centered Gaussian density has the logarithmic derivative
needed for the entrance-law calculation. -/
theorem hasDerivAt_gaussianPDFReal_zero (t : ℝ≥0) (ht : t ≠ 0) (y : ℝ) :
    HasDerivAt (gaussianPDFReal 0 t) (-(y / (t : ℝ)) * gaussianPDFReal 0 t y) y := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  have h := ((((hasDerivAt_id y).pow 2).neg.div_const (2 * (t : ℝ))).exp).const_mul
    (Real.sqrt (2 * Real.pi * t))⁻¹
  convert h using 1
  · ext x
    simp [gaussianPDFReal]
  · simp only [gaussianPDFReal, sub_zero, Pi.neg_apply, Pi.pow_apply, id_eq]
    field_simp
    ring

/-- The entrance density of the killed drifted Brownian transition formula
is the right-hand limit of the displayed conditioned transition density, with
the centered Gaussian density of variance `t`.  This is an analytic limit; it
does not assert that either expression is a law. -/
theorem tendsto_gaussian_conditioned_entrance_density
    (d y : ℝ) (t : ℝ≥0) (hd : d ≠ 0) (ht : t ≠ 0) :
    Tendsto (fun x =>
      (Real.exp (d * (y - x) - d ^ 2 * (t : ℝ) / 2) *
        (gaussianPDFReal 0 t (y - x) - gaussianPDFReal 0 t (y + x))) *
        (1 - Real.exp (-2 * d * y)) / (1 - Real.exp (-2 * d * x)))
      (𝓝[>] 0)
      (𝓝 ((y / (d * (t : ℝ))) * gaussianPDFReal 0 t y *
        Real.exp (d * y - d ^ 2 * (t : ℝ) / 2) * (1 - Real.exp (-2 * d * y)))) :=
  tendsto_conditioned_entrance_density (gaussianPDFReal 0 t) d t y hd
    (by exact_mod_cast ht) (hasDerivAt_gaussianPDFReal_zero t ht y)

/-- Adding a positive linear drift to a sublinear path makes it tend to
positive infinity. -/
theorem tendsto_add_pos_drift_of_sublinear (f : ℝ → ℝ) (d : ℝ) (hd : 0 < d)
    (hf : Tendsto (fun t => f t / t) atTop (𝓝 0)) :
    Tendsto (fun t => f t + d * t) atTop atTop := by
  have hsmall : ∀ᶠ t : ℝ in atTop, -(d / 2) < f t / t :=
    hf.eventually (lt_mem_nhds (by linarith))
  have hlower : (fun t : ℝ => (d / 2) * t) ≤ᶠ[atTop] fun t => f t + d * t := by
    filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with t ht ht1
    have htpos : 0 < t := by linarith
    have hbound := (lt_div_iff₀ htpos).mp ht
    nlinarith
  exact tendsto_atTop_mono' atTop hlower
    ((tendsto_const_mul_atTop_of_pos (by linarith : 0 < d / 2)).2 tendsto_id)

/-- A continuous path starting at zero and tending to positive infinity
attains zero at its last zero and is strictly positive thereafter. -/
theorem lastZeroR_eq_zero_and_pos {c : ℝ → ℝ} (hc : Continuous c) (hc0 : c 0 = 0)
    (htend : Tendsto c atTop atTop) :
    let ℓ := MatedCRTHarmonic.MatedCRT.lastZeroR c
    0 ≤ ℓ ∧ c ℓ = 0 ∧ ∀ t, ℓ < t → 0 < c t := by
  obtain ⟨R, hR⟩ := eventually_atTop.1 (htend.eventually_gt_atTop 0)
  let Z : Set ℝ := {s | 0 ≤ s ∧ c s = 0}
  have hZne : Z.Nonempty := ⟨0, le_rfl, hc0⟩
  have hZclosed : IsClosed Z := isClosed_Ici.inter (isClosed_eq hc continuous_const)
  have hZbdd : BddAbove Z := by
    refine ⟨R, ?_⟩
    intro s hs
    by_contra h
    have := hR s (le_of_lt (lt_of_not_ge h))
    exact (ne_of_gt this) hs.2
  have hlast : sSup Z ∈ Z := hZclosed.csSup_mem hZne hZbdd
  refine ⟨hlast.1, hlast.2, ?_⟩
  intro t ht
  change sSup Z < t at ht
  by_contra hneg
  let u := max t R + 1
  have htu : t ≤ u := by dsimp [u]; linarith [le_max_left t R]
  have hRu : R ≤ u := by dsimp [u]; linarith [le_max_right t R]
  have hcu : 0 < c u := hR u hRu
  obtain ⟨v, hv, hcv⟩ := intermediate_value_Icc htu hc.continuousOn
    ⟨le_of_not_gt hneg, le_of_lt hcu⟩
  have hvZ : v ∈ Z := ⟨le_trans hlast.1 (le_trans (le_of_lt ht) hv.1), hcv⟩
  have hvle : v ≤ sSup Z := le_csSup hZbdd hvZ
  linarith [hv.1]

/-- A continuous path tending to `+∞` has a zero at or after any point where it is `≤ 0`
(intermediate value theorem). -/
theorem exists_zero_ge_of_nonpos {c : ℝ → ℝ} (hc : Continuous c)
    (htend : Tendsto c atTop atTop) {u : ℝ} (hu : c u ≤ 0) :
    ∃ v, u ≤ v ∧ c v = 0 := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 (htend.eventually_ge_atTop 1)
  have hx : 0 ≤ c (max u T) := by linarith [hT (max u T) (le_max_right u T)]
  obtain ⟨v, hv, hcv⟩ := intermediate_value_Icc (le_max_left u T) hc.continuousOn ⟨hu, hx⟩
  exact ⟨v, hv.1, hcv⟩

/-- For a path tending to `+∞`, a nonpositive value at some `u ≥ q` is equivalent to: for every
`k`, a rational `a > q` with value below `1/(k+1)`. -/
theorem exists_nonpos_iff_rat {c : ℝ → ℝ} (hc : Continuous c)
    (htend : Tendsto c atTop atTop) (q : ℝ) :
    (∃ u, q ≤ u ∧ c u ≤ 0) ↔
      ∀ k : ℕ, ∃ a : ℚ, q < (a : ℝ) ∧ c (a : ℝ) < 1 / ((k : ℝ) + 1) := by
  constructor
  · rintro ⟨u, hqu, hu⟩ k
    have hlt : c u < 1 / ((k : ℝ) + 1) := lt_of_le_of_lt hu (by positivity)
    have hev : ∀ᶠ x in 𝓝 u, c x < 1 / ((k : ℝ) + 1) :=
      hc.continuousAt.eventually_lt continuousAt_const hlt
    obtain ⟨v, hv, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
      (nhdsWithin_le_nhds hev)
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (Set.mem_Ioi.1 hv)
    exact ⟨a, lt_of_le_of_lt hqu ha1, hsub ⟨ha1, ha2⟩⟩
  · intro H
    obtain ⟨T, hT⟩ := eventually_atTop.1 (htend.eventually_ge_atTop 1)
    have hqM : q ≤ max T q := le_max_right T q
    obtain ⟨u, hu, hmin⟩ := (isCompact_Icc : IsCompact (Set.Icc q (max T q))).exists_isMinOn
      ⟨q, ⟨le_refl q, hqM⟩⟩ hc.continuousOn
    refine ⟨u, hu.1, ?_⟩
    by_contra hpos
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (not_le.mp hpos)
    obtain ⟨a, ha1, ha2⟩ := H k
    have ha_le : (a : ℝ) ≤ max T q := by
      by_contra hcon
      have hcon' : max T q < (a : ℝ) := not_le.mp hcon
      have h1 : 1 ≤ c (a : ℝ) := hT (a : ℝ) (le_trans (le_max_left T q) (le_of_lt hcon'))
      have hk1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      linarith
    have hle : c u ≤ c (a : ℝ) := isMinOn_iff.1 hmin (a : ℝ) ⟨le_of_lt ha1, ha_le⟩
    linarith

/-- Changing from logarithmic radius to radius preserves the largest level,
provided the logarithmic level set is nonempty and bounded above. -/
theorem exp_sSup_level_eq_sSup_positive_level (f : ℝ → ℝ) (c : ℝ)
    (hne : {s : ℝ | f s = c}.Nonempty) (hbounded : BddAbove {s : ℝ | f s = c}) :
    Real.exp (sSup {s : ℝ | f s = c}) =
      sSup {r : ℝ | 0 < r ∧ f (Real.log r) = c} := by
  have himage : Real.exp '' {s : ℝ | f s = c} =
      {r : ℝ | 0 < r ∧ f (Real.log r) = c} := by
    ext r
    constructor
    · rintro ⟨s, hs, rfl⟩
      change f s = c at hs
      exact ⟨Real.exp_pos s, by simpa only [Real.log_exp] using hs⟩
    · rintro ⟨hr, hf⟩
      exact ⟨Real.log r, hf, Real.exp_log hr⟩
  rw [Monotone.map_csSup_of_continuousAt Real.continuous_exp.continuousAt
    Real.exp_monotone hne hbounded, himage]

open scoped Classical in
/-- For a path tending to `+∞`, the last zero `sup {s ≥ 0 : c s = 0}` is the supremum of the rational
levels `q ≥ 0` at which `c` is nonpositive somewhere at or after `q`; the supremum over an empty family
is `0`. -/
theorem lastZeroR_eq_iSup_rat {c : ℝ → ℝ} (hc : Continuous c)
    (htend : Tendsto c atTop atTop) :
    (⨆ q : ℚ, if (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0 then (q : ℝ) else 0) =
      MatedCRTHarmonic.MatedCRT.lastZeroR c := by
  unfold MatedCRTHarmonic.MatedCRT.lastZeroR
  obtain ⟨R, hR⟩ := eventually_atTop.1 (htend.eventually_gt_atTop 0)
  have hZbdd : BddAbove {s : ℝ | 0 ≤ s ∧ c s = 0} := by
    refine ⟨R, fun s hs => ?_⟩
    by_contra h
    have h1 : 0 < c s := hR s (le_of_lt (not_le.mp h))
    linarith [hs.2]
  have hZcl : IsClosed {s : ℝ | 0 ≤ s ∧ c s = 0} :=
    (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).inter (isClosed_eq hc continuous_const)
  by_cases hZne : ({s : ℝ | 0 ≤ s ∧ c s = 0} : Set ℝ).Nonempty
  · have hs : sSup {s : ℝ | 0 ≤ s ∧ c s = 0} ∈ {s : ℝ | 0 ≤ s ∧ c s = 0} :=
      hZcl.csSup_mem hZne hZbdd
    have hsnn : 0 ≤ sSup {s : ℝ | 0 ≤ s ∧ c s = 0} := hs.1
    have hsz : c (sSup {s : ℝ | 0 ≤ s ∧ c s = 0}) = 0 := hs.2
    have hA : ∀ q : ℚ, (0 : ℝ) ≤ (q : ℝ) →
        ((∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0) ↔ (q : ℝ) ≤ sSup {s : ℝ | 0 ≤ s ∧ c s = 0}) := by
      intro q hq
      constructor
      · rintro ⟨u, hqu, hu⟩
        obtain ⟨v, huv, hv⟩ := exists_zero_ge_of_nonpos hc htend hu
        have hvZ : v ∈ {s : ℝ | 0 ≤ s ∧ c s = 0} := ⟨le_trans hq (le_trans hqu huv), hv⟩
        exact le_trans (le_trans hqu huv) (le_csSup hZbdd hvZ)
      · intro hqs
        exact ⟨sSup {s : ℝ | 0 ≤ s ∧ c s = 0}, hqs, le_of_eq hsz⟩
    have hterm_le : ∀ q : ℚ, (if (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0
        then (q : ℝ) else 0) ≤ sSup {s : ℝ | 0 ≤ s ∧ c s = 0} := by
      intro q
      split_ifs with h
      · exact (hA q h.1).1 h.2
      · exact hsnn
    have hterm_nonneg : ∀ q : ℚ, (0 : ℝ) ≤ (if (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0
        then (q : ℝ) else 0) := by
      intro q
      split_ifs with h
      · exact h.1
      · exact le_rfl
    have hbdd : BddAbove (Set.range fun q : ℚ => (if (0 : ℝ) ≤ (q : ℝ) ∧
        ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0 then (q : ℝ) else 0)) :=
      ⟨sSup {s : ℝ | 0 ≤ s ∧ c s = 0}, by rintro _ ⟨q, rfl⟩; exact hterm_le q⟩
    apply le_antisymm
    · exact ciSup_le hterm_le
    · by_contra hlt
      have hlt' : (⨆ q : ℚ, if (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0
          then (q : ℝ) else 0) < sSup {s : ℝ | 0 ≤ s ∧ c s = 0} := not_le.mp hlt
      have hM0 : (0 : ℝ) ≤ ⨆ q : ℚ, (if (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0
          then (q : ℝ) else 0) := le_trans (hterm_nonneg 0) (le_ciSup hbdd 0)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt'
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := le_trans hM0 (le_of_lt hq1)
      have hqterm : (if (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0
          then (q : ℝ) else 0) = (q : ℝ) := by
        split_ifs with h
        · rfl
        · exact absurd ⟨hq0, (hA q hq0).2 (le_of_lt hq2)⟩ h
      have hle : (if (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0
          then (q : ℝ) else 0) ≤ ⨆ q : ℚ, (if (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0
          then (q : ℝ) else 0) := le_ciSup hbdd q
      linarith
  · have hZempty : ({s : ℝ | 0 ≤ s ∧ c s = 0} : Set ℝ) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hZne
    have hzero : ∀ q : ℚ, (if (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, (q : ℝ) ≤ u ∧ c u ≤ 0
        then (q : ℝ) else 0) = 0 := by
      intro q
      split_ifs with h
      · obtain ⟨hq0, u, hqu, hu⟩ := h
        obtain ⟨v, huv, hv⟩ := exists_zero_ge_of_nonpos hc htend hu
        have hvZ : v ∈ ({s : ℝ | 0 ≤ s ∧ c s = 0} : Set ℝ) :=
          ⟨le_trans hq0 (le_trans hqu huv), hv⟩
        rw [hZempty] at hvZ
        simp at hvZ
      · rfl
    simp only [hzero, ciSup_const, hZempty, Real.sSup_empty]

/-- The path space of continuous maps `ℝ≥0 → ℝ` with its evaluation (coordinate)
process: a finite measure on paths is determined by the law of its coordinate
process. -/
theorem continuousPath_measure_ext_of_coordinate_law
    {μ ν : Measure C(ℝ≥0, ℝ)}
    (h : μ.map (fun w (t : ℝ≥0) => w t) = ν.map (fun w (t : ℝ≥0) => w t)) :
    μ = ν := by
  let e : C(ℝ≥0, ℝ) → (ℝ≥0 → ℝ) := fun w t => w t
  have he : Measurable e := Measurable.of_eval fun t => ContinuousMap.measurable_eval t
  have hcomap : (inferInstance : MeasurableSpace C(ℝ≥0, ℝ)) ≤
      (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)).comap e := by
    change (ContinuousMap.measurableSpace : MeasurableSpace C(ℝ≥0, ℝ)) ≤ _
    rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
    refine iSup_le fun t => ?_
    apply measurable_iff_comap_le.mp
    exact (measurable_pi_apply t).comp (comap_measurable e)
  apply Measure.ext
  intro A hA
  obtain ⟨B, hB, hpre⟩ := MeasurableSpace.measurableSet_comap.mp (hcomap A hA)
  have hBeq := congrArg (fun m : Measure (ℝ≥0 → ℝ) => m B) h
  rw [Measure.map_apply he hB, Measure.map_apply he hB, hpre] at hBeq
  exact hBeq

/-- A measurable coordinate process with almost surely continuous paths has
a measurable continuous-path version. -/
theorem exists_measurable_continuousPath_version
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (Z : Ω → (ℝ≥0 → ℝ))
    (hZ : Measurable Z) (hc : ∀ᵐ ω ∂P, Continuous (Z ω)) :
    ∃ Y : Ω → C(ℝ≥0, ℝ),
      Measurable Y ∧ ∀ᵐ ω ∂P, (fun t => Y ω t) = Z ω := by
  classical
  have hnull : P {ω | ¬ Continuous (Z ω)} = 0 := ae_iff.mp hc
  obtain ⟨N, hsub, hN, hNzero⟩ := exists_measurable_superset_of_null hnull
  let Y : Ω → C(ℝ≥0, ℝ) := fun ω =>
    if hω : ω ∈ N then 0 else ⟨Z ω, by
      by_contra h
      exact hω (hsub h)⟩
  have hm : Measurable Y := ContinuousMap.measurable_iff_eval.mpr fun t => by
    have heq : (fun ω => Y ω t) = fun ω => if ω ∈ N then 0 else Z ω t := by
      funext ω
      by_cases hω : ω ∈ N <;> simp [Y, hω]
    rw [heq]
    exact measurable_const.ite hN ((measurable_pi_apply t).comp hZ)
  refine ⟨Y, hm, ?_⟩
  have hgood : ∀ᵐ ω ∂P, ω ∉ N := ae_iff.mpr (by simpa using hNzero)
  filter_upwards [hgood] with ω hω
  simp [Y, hω]

end LatticeProb.ContinuousPathLaw

end
