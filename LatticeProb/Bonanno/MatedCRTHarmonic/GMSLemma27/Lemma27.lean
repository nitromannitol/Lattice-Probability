/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSLemma27.Lemma27 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Lemma28
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.SLEInterfaces

/-!
# [18] Lemma 2.7: maximal cell diameter

[18] Lemma 2.7: for `q ∈ (0, 2/(2+γ)²)`, `ρ ∈ (0, 1)` and `ε ∈ (0, 1)`,
`P[diam(H^ε_x) ≤ ε^q, ∀ x ∈ V_{G^ε}(B_ρ(0))] ≥ 1 − ε^{α(q,γ)+o_ε(1)}` with
`α(q, γ) = (q/(2γ²))(1/q − 2 − γ²/2)² − 2q`, proved as in `[18]` with a strict mass comparison and a sub-segment argument: the strict mass comparison comes from Lemma 2.8 with `p` slightly below `1/q̃ − 2 − γ²/2`, and a cell
meeting `B_ρ(0)` is handled through a sub-segment inside `B̄_{ε^{q₁}}(η(s)) ⊂ B_{(1+ρ)/2}(0)`.

* `lemma27_segments` — every segment `η([a, b])` with `b − a ≤ ε` meeting `B_ρ(0)` has diameter `≤ ε^q`, outside an
  event of probability `≤ C ε^α`, for every `α < α(q, γ)`;
* `lemma27` — (2.9) as printed, for the cells `H^ε_x = η([ε(x−1), εx])`.

Inputs: `SegmentsContainBalls M` ( bundle input), `GMCLowerTail γ` and `AreaDominatesWholePlaneGFF M` (SLE-free, to
prove).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMSLemma27

/-- The exponent `α(q, γ) = (q/(2γ²))(1/q − 2 − γ²/2)² − 2q` of [18] Lemma 2.7. -/
def lemma27Exponent (q γ : ℝ) : ℝ := q / (2 * γ ^ 2) * (1 / q - 2 - γ ^ 2 / 2) ^ 2 - 2 * q

theorem lemma27Exponent_eq (q γ : ℝ) :
    lemma27Exponent q γ = q * ((1 / q - (2 + γ ^ 2 / 2)) ^ 2 / (2 * γ ^ 2) - 2) := by
  unfold lemma27Exponent; ring

/-- `2/(2+γ)² < 1/(2 + γ²/2)`: the upper limit for `q` makes `1/q − 2 − γ²/2 > 2γ` . -/
theorem two_mul_lt_of_lt_lemma27Bound {q γ : ℝ} (hγ : 0 < γ) (hq : 0 < q) (hq' : q < 2 / (2 + γ) ^ 2) :
    2 * γ < 1 / q - (2 + γ ^ 2 / 2) := by
  have h1 : q * (2 + γ) ^ 2 < 2 := (lt_div_iff₀ (by positivity)).mp hq'
  have h2 : (2 + γ) ^ 2 / 2 < 1 / q := by
    rw [lt_div_iff₀ hq]; nlinarith
  nlinarith

/-- `α(q, γ) > 0` for `q ∈ (0, 2/(2+γ)²)`. -/
theorem lemma27Exponent_pos {q γ : ℝ} (hγ : 0 < γ) (hq : 0 < q) (hq' : q < 2 / (2 + γ) ^ 2) :
    0 < lemma27Exponent q γ := by
  rw [lemma27Exponent_eq]
  have hX := two_mul_lt_of_lt_lemma27Bound hγ hq hq'
  have h4 : (2 * γ) ^ 2 < (1 / q - (2 + γ ^ 2 / 2)) ^ 2 := pow_lt_pow_left₀ hX (by positivity) two_ne_zero
  have h5 : 2 < (1 / q - (2 + γ ^ 2 / 2)) ^ 2 / (2 * γ ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  exact mul_pos hq (by linarith)

/-- Choice of `q̃ ∈ (q, 2/(2+γ)²)` with `α(q̃, γ) > α` ([18], "sending `q̃ → q`"). -/
theorem exists_lemma27_qtilde {q γ α : ℝ} (hq : 0 < q) (hq' : q < 2 / (2 + γ) ^ 2)
    (hα : α < lemma27Exponent q γ) :
    ∃ qt : ℝ, q < qt ∧ qt < 2 / (2 + γ) ^ 2 ∧ α < lemma27Exponent qt γ := by
  have hc : ContinuousAt (fun x : ℝ => lemma27Exponent x γ) q := by
    unfold lemma27Exponent
    fun_prop (disch := exact hq.ne')
  have h1 : ∀ᶠ x in 𝓝[>] q, α < lemma27Exponent x γ :=
    (hc.tendsto.eventually (lt_mem_nhds hα)).filter_mono nhdsWithin_le_nhds
  have h2 : ∀ᶠ x in 𝓝[>] q, x < 2 / (2 + γ) ^ 2 := (gt_mem_nhds hq').filter_mono nhdsWithin_le_nhds
  obtain ⟨x, ⟨hx1, hx2⟩, hx3⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
  exact ⟨x, hx3, hx2, hx1⟩

variable {γ : ℝ}

/-- The event of [18] Lemma 2.7 for all segments: every segment `η([a, b])` of time length `b − a ≤ ε` that meets
`B_ρ(0)` has diameter at most `ε^q`. -/
def segmentDiamGood (M : CellModel γ) (ε q ρ : ℝ) : Set M.Ω :=
  {ω | ∀ a b : ℝ, b - a ≤ ε → (M.curve ω '' Icc a b ∩ ball (0 : ℂ) ρ).Nonempty →
    diam (M.curve ω '' Icc a b) ≤ ε ^ q}

/-- The event of [18] Lemma 2.7 (2.9): every cell `H^ε_x` meeting `B_ρ(0)` has diameter at most `ε^q`. -/
def cellDiamGood (M : CellModel γ) (ε q ρ : ℝ) : Set M.Ω :=
  {ω | ∀ x : ℤ, (M.cell ε ω x ∩ ball (0 : ℂ) ρ).Nonempty → diam (M.cell ε ω x) ≤ ε ^ q}

theorem segmentDiamGood_subset_cellDiamGood (M : CellModel γ) (ε q ρ : ℝ) :
    segmentDiamGood M ε q ρ ⊆ cellDiamGood M ε q ρ := by
  intro ω hω x hx
  exact hω _ _ (le_of_eq (by ring)) hx

/-- **[18] Lemma 2.7 for all segments** ([18]). For `γ > 0`, `q ∈ (0, 2/(2+γ)²)`,
`ρ ∈ (0, 1)` and every `α < α(q, γ)` there is `C` such that for all `ε ∈ (0, 1)`, outside an event of probability
`≤ C ε^α`, every segment `η([a, b])` with `b − a ≤ ε` meeting `B_ρ(0)` has diameter `≤ ε^q`. -/
theorem lemma27_segments (M : CellModel γ) (hSLE : SegmentsContainBalls M) (hGMC : GMCLowerTail γ)
    (hdom : AreaDominatesWholePlaneGFF M) (hγ : 0 < γ) {q ρ α : ℝ} (hq : 0 < q)
    (hq' : q < 2 / (2 + γ) ^ 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα : α < lemma27Exponent q γ) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1, M.P (segmentDiamGood M ε q ρ)ᶜ ≤ ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨qt, hqqt, hqt', hαqt⟩ := exists_lemma27_qtilde hq hq' hα
  have hqt0 : 0 < qt := hq.trans hqqt
  set x₀ : ℝ := 2 + γ ^ 2 / 2 with hx₀
  set p : ℝ := 1 / qt - x₀ with hp
  have hp0 : 0 < p := by
    have := two_mul_lt_of_lt_lemma27Bound hγ hqt0 hqt'
    rw [hp]; linarith
  set e : ℝ := α / qt with he
  have hep : e < p ^ 2 / (2 * γ ^ 2) - 2 := by
    rw [lemma27Exponent_eq] at hαqt
    rw [he, div_lt_iff₀ hqt0]
    linarith
  set ρ' : ℝ := (1 + ρ) / 2 with hρ'
  obtain ⟨C₈, hC₈⟩ := lemma28_strict M hGMC hdom hγ hp0 (ρ := ρ') (by rw [hρ']; linarith)
    (by rw [hρ']; linarith) hep
  set q₁ : ℝ := (q + qt) / 2 with hq₁
  have hq₁0 : 0 < q₁ := by rw [hq₁]; linarith
  set r : ℝ := 1 - q₁ / qt with hr
  have hr01 : r ∈ Ioo (0 : ℝ) 1 := by
    have h1 : q₁ / qt < 1 := (div_lt_one hqt0).mpr (by rw [hq₁]; linarith)
    have h2 : 0 < q₁ / qt := div_pos hq₁0 hqt0
    exact ⟨by rw [hr]; linarith, by rw [hr]; linarith⟩
  -- the SLE input at scale `ε^{q̃}`
  have hsle : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (M.P (segmentBallEvent M 1 r (ε ^ qt))ᶜ).toReal ≤ (ε ^ qt) ^ (α / qt) :=
    (tendsto_rpow_nhdsGT_zero hqt0).eventually
      (eventually_le_rpow_of_isLittleO (hSLE r hr01 1 one_pos (α / qt)))
  have hev1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 := eventually_lt_nhdsGT_zero one_pos
  have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (q₁ - q) < 1 / 2 :=
    eventually_rpow_lt (by rw [hq₁]; linarith) (by norm_num)
  have hev3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ q₁ < (1 - ρ) / 2 :=
    eventually_rpow_lt hq₁0 (by linarith)
  refine exists_bound_of_eventually (C₀ := 1 + |C₈|) (fun ε => prob_le_one) ?_
  filter_upwards [hsle, hev1, hev2, hev3, self_mem_nhdsWithin] with ε hs h1 h2 h3 hε0
  have hε : 0 < ε := hε0
  set δ : ℝ := ε ^ qt with hδ
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hε qt
  have hδ1 : δ < 1 := Real.rpow_lt_one hε.le h1 hqt0
  have hδα : δ ^ (α / qt) = ε ^ α := by
    rw [hδ, ← Real.rpow_mul hε.le]; congr 1; field_simp
  have hδD : δ ^ (1 - r) = ε ^ q₁ := by
    rw [hδ, ← Real.rpow_mul hε.le]; congr 1; rw [hr]; field_simp; ring
  have hδm : δ ^ (x₀ + p) = ε := by
    rw [hδ, ← Real.rpow_mul hε.le, hp]
    have : qt * (x₀ + (1 / qt - x₀)) = 1 := by field_simp; ring
    rw [this, Real.rpow_one]
  have hDq : 2 * ε ^ q₁ ≤ ε ^ q := by
    have e1 : ε ^ q₁ = ε ^ (q₁ - q) * ε ^ q := by rw [← Real.rpow_add hε]; congr 1; ring
    rw [e1]
    have := Real.rpow_pos_of_pos hε q
    nlinarith
  -- the good event contains the intersection of the two input events, almost surely
  set B₈ : Set M.Ω := {ω | ∃ z ∈ ball (0 : ℂ) ρ', M.area ω (ball z δ) ≤ ENNReal.ofReal (δ ^ (x₀ + p))}
    with hB₈
  have hcover : (segmentDiamGood M ε q ρ)ᶜ ≤ᵐ[M.P] (segmentBallEvent M 1 r δ)ᶜ ∪ B₈ := by
    filter_upwards [M.ae_continuous_curve, M.ae_area_curve] with ω hc ha
    intro hω
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨hE1, hE2⟩ := hcon
    apply hω
    intro a b hba hmeet
    have hball : ∀ a b : ℝ, a < b → M.curve ω '' Icc a b ⊆ ball (0 : ℂ) 1 →
        ε ^ q₁ ≤ diam (M.curve ω '' Icc a b) →
          ∃ c : ℂ, ∃ t : ℝ, δ ≤ t ∧ ball c t ⊆ M.curve ω '' Icc a b := by
      intro a b hab hsub hdiam
      exact hE1 δ ⟨hδ0, le_rfl⟩ a b hab hsub (by rw [hδD]; exact hdiam)
    have hmass : ∀ z ∈ ball (0 : ℂ) ρ', ENNReal.ofReal ε < M.area ω (ball z δ) := by
      intro z hz
      by_contra hle
      exact hE2 ⟨z, hz, by rw [hδm]; exact not_lt.mp hle⟩
    have hdiam := diam_segment_le_of_balls hc ha (Real.rpow_pos_of_pos hε q₁) hδ0
      (by rw [hρ']; linarith) (by rw [hρ']; linarith) hball hmass hba hmeet
    exact hdiam.trans hDq
  calc M.P (segmentDiamGood M ε q ρ)ᶜ ≤ M.P ((segmentBallEvent M 1 r δ)ᶜ ∪ B₈) :=
        measure_mono_ae hcover
    _ ≤ M.P (segmentBallEvent M 1 r δ)ᶜ + M.P B₈ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε ^ α) + ENNReal.ofReal (|C₈| * ε ^ α) := by
        gcongr
        · exact measure_le_ofReal_of_toReal_le (hs.trans (le_of_eq hδα))
        · refine (hC₈ δ ⟨hδ0, hδ1⟩).trans (ENNReal.ofReal_le_ofReal ?_)
          rw [show δ ^ e = ε ^ α from hδα]
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hε.le _)
    _ = ENNReal.ofReal ((1 + |C₈|) * ε ^ α) := by
        rw [← ENNReal.ofReal_add (Real.rpow_nonneg hε.le _)
          (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hε.le _))]
        ring_nf

/-- **[18] Lemma 2.7** ((2.9), `[18]`) for the cells `H^ε_x = η([ε(x−1), εx])` of the cell model: for `γ > 0`,
`q ∈ (0, 2/(2+γ)²)`, `ρ ∈ (0, 1)`, `ε ∈ (0, 1)`, `P[diam(H^ε_x) ≤ ε^q, ∀ x ∈ V_{G^ε}(B_ρ(0))] ≥ 1 − ε^{α(q,γ)+o_ε(1)}`,
the `o_ε(1)` read as: for every `α < α(q, γ)` there is `C` (depending on `q, ρ, γ, α`) with the bound `1 − C ε^α`
for all `ε ∈ (0, 1)`. Inputs: `SegmentsContainBalls M` ( bundle input), `GMCLowerTail γ`,
`AreaDominatesWholePlaneGFF M` (SLE-free, to prove). -/
theorem lemma27 (M : CellModel γ) (hSLE : SegmentsContainBalls M) (hGMC : GMCLowerTail γ)
    (hdom : AreaDominatesWholePlaneGFF M) (hγ : 0 < γ) {q ρ α : ℝ} (hq : 0 < q)
    (hq' : q < 2 / (2 + γ) ^ 2) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hα : α < lemma27Exponent q γ) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1, 1 - ENNReal.ofReal (C * ε ^ α) ≤ M.P (cellDiamGood M ε q ρ) := by
  obtain ⟨C, hC⟩ := lemma27_segments M hSLE hGMC hdom hγ hq hq' hρ.1 hρ.2 hα
  exact ⟨C, fun ε hε => one_sub_le_measure_of_compl_le
    ((measure_mono (compl_subset_compl.mpr (segmentDiamGood_subset_cellDiamGood M ε q ρ))).trans
      (hC ε hε))⟩

end MatedCRTHarmonic.GMSLemma27
