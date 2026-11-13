/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46SCoverage at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.CellArea
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Lemma46

/-!
# Coverage confines visits of the interior

For an area-parametrized continuous curve, covering an open ball by one time
interval also confines *all* visits to that ball to that interval. A later
short curve segment inside the ball would have positive area and lie in the
earlier segment's image, contradicting area-null overlap of time-disjoint
segments. This upgrades the bundle's unit-disk coverage field to the form
needed for the graph-degree union bound.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

/-- A positive-length interval cannot be contained in an earlier disjoint
interval's image when the curve is parametrized by area. -/
theorem no_positive_interval_in_disjoint_past {μ : Measure ℂ}
    (η : C(ℝ, ℂ))
    (hpar : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s))
    {a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c < d)
    (hsub : η '' Icc c d ⊆ η '' Icc a b) : False := by
  have hnull := CellScaling.measure_image_inter_eq_zero hpar hab hbc hcd.le
  have hinter : η '' Icc a b ∩ η '' Icc c d = η '' Icc c d :=
    inter_eq_right.mpr hsub
  rw [hinter, hpar c d hcd.le] at hnull
  exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hcd)).ne' hnull

/-- Once an open ball is covered by a compact time interval, all of its
preimages occur in that interval. -/
theorem preimage_ball_subset_covered_interval {μ : Measure ℂ}
    (η : C(ℝ, ℂ))
    (hpar : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s))
    {R a b : ℝ} (hab : a ≤ b)
    (hcover : ball (0 : ℂ) R ⊆ η '' Icc a b) :
    η ⁻¹' ball (0 : ℂ) R ⊆ Icc a b := by
  intro t ht
  have hopen : IsOpen (η ⁻¹' ball (0 : ℂ) R) := isOpen_ball.preimage η.continuous
  obtain ⟨δ, hδ, hδball⟩ := Metric.isOpen_iff.mp hopen t ht
  by_contra hnot
  rcases not_and_or.mp hnot with hleft | hright
  · have hseg : η '' Icc (t - δ / 2) t ⊆ η '' Icc a b := by
      rintro z ⟨u, hu, rfl⟩
      apply hcover
      apply hδball
      rw [Metric.mem_ball, Real.dist_eq]
      have : |u - t| ≤ δ / 2 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
      linarith
    have hnull := CellScaling.measure_image_inter_eq_zero hpar
      (show t - δ / 2 ≤ t by linarith) (show t ≤ a by linarith)
      hab
    have hinter : η '' Icc (t - δ / 2) t ∩ η '' Icc a b =
        η '' Icc (t - δ / 2) t := inter_eq_left.mpr hseg
    rw [hinter, hpar (t - δ / 2) t (by linarith)] at hnull
    exact (ENNReal.ofReal_pos.mpr (by linarith : 0 < t - (t - δ / 2))).ne' hnull
  · have hseg : η '' Icc t (t + δ / 2) ⊆ η '' Icc a b := by
      rintro z ⟨u, hu, rfl⟩
      apply hcover
      apply hδball
      rw [Metric.mem_ball, Real.dist_eq]
      have : |u - t| ≤ δ / 2 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
      linarith
    exact no_positive_interval_in_disjoint_past η hpar hab (by linarith)
      (by linarith) hseg

/-- If every visit to a disk is confined to `[-M,M]`, each mesh cell
containing a point of that disk has an index in a finite interval of size
`O(M/ε)`. -/
theorem cell_index_mem_interval_of_preimage_ball_bound {η : ℝ → ℂ}
    {ε M R : ℝ} (hε : 0 < ε)
    (hconf : η ⁻¹' ball (0 : ℂ) R ⊆ Icc (-M) M)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R)
    {x : ℤ} (hx : z ∈ cellOf ε η x) :
    x ∈ Icc ⌈-M / ε⌉ (⌈M / ε⌉ + 1) := by
  obtain ⟨t, ht, hηt⟩ := hx
  have htM : t ∈ Icc (-M) M := hconf (by change η t ∈ ball (0 : ℂ) R; rw [hηt]; exact hz)
  have hlow : -M / ε ≤ (x : ℝ) := by
    apply (div_le_iff₀ hε).2
    nlinarith [ht.2, htM.1]
  have hhigh : (x : ℝ) ≤ M / ε + 1 := by
    have hx' : (x : ℝ) - 1 ≤ t / ε := by
      apply (le_div_iff₀ hε).2
      nlinarith [ht.1]
    have ht' : t / ε ≤ M / ε := (div_le_div_of_nonneg_right htM.2 hε.le)
    linarith
  constructor
  · exact Int.ceil_le.mpr hlow
  · have hceil := Int.le_ceil (M / ε)
    have : (x : ℝ) ≤ (⌈M / ε⌉ : ℤ) + 1 := by linarith
    exact_mod_cast this

end MatedCRTHarmonic.GMS4b
