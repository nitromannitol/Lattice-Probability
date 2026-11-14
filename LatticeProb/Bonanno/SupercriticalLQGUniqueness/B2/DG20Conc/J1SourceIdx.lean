/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceIdx at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1NearbyIdx
import Mathlib.Topology.MetricSpace.Thickening

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

def j1SourceSquarePred (K : ℕ) (δ : ℝ) (b : ℤ × ℤ) : Prop :=
  T20.dyBlock K b ⊆ thickening δ L23.sq01

theorem j1_center_mem_dyBlock (K : ℕ) (b : ℤ × ℤ) :
    T20.dyCenter K b ∈ T20.dyBlock K b := by
  have hr : 0 < (2 : ℝ)⁻¹ ^ K := by positivity
  simp only [T20.dyBlock, T20.dyCenter, Complex.mem_reProdIm,
    mem_Icc]
  constructor <;> constructor <;> nlinarith

theorem j1_center_mem_hoBlock (K : ℕ) (b : ℤ × ℤ) :
    T20.dyCenter K b ∈ T20B.hoBlock K b := by
  have hp : (2 : ℝ)⁻¹ ^ K * (2 : ℝ)^K = 1 := by
    rw [← mul_pow]
    norm_num
  change ⌊(((b.1 : ℝ) + 1 / 2) * (2 : ℝ)⁻¹ ^ K) * 2 ^ K⌋ = b.1 ∧
    ⌊(((b.2 : ℝ) + 1 / 2) * (2 : ℝ)⁻¹ ^ K) * 2 ^ K⌋ = b.2
  rw [mul_assoc, hp, mul_one, mul_assoc, hp, mul_one]
  constructor <;> apply Int.floor_eq_iff.mpr <;> constructor <;> norm_num

theorem j1_source_center_near_square {K : ℕ} {δ : ℝ}
    {b : ℤ × ℤ} (hb : j1SourceSquarePred K δ b) :
    ∃ z ∈ L23.sq01, dist (T20.dyCenter K b) z < δ := by
  exact (mem_thickening_iff.mp (hb (j1_center_mem_dyBlock K b)))

theorem j1_source_center_nearbyBox {K : ℕ} {δ : ℝ}
    {b : ℤ × ℤ} (hb : j1SourceSquarePred K δ b)
    (hδ : δ ≤ 1 / 4) : T20.dyCenter K b ∈ j1NearbyBox := by
  obtain ⟨z, hz, hdist⟩ := j1_source_center_near_square hb
  rw [L23.mem_sq01] at hz
  simp only [mem_Icc] at hz
  have hre := Complex.abs_re_le_norm (T20.dyCenter K b - z)
  have him := Complex.abs_im_le_norm (T20.dyCenter K b - z)
  rw [Complex.sub_re, abs_le] at hre
  rw [Complex.sub_im, abs_le] at him
  rw [dist_eq_norm] at hdist
  simp only [j1NearbyBox, Complex.mem_reProdIm, mem_Icc]
  exact ⟨⟨by linarith [hre.1], by linarith [hre.2]⟩,
    by linarith [him.1], by linarith [him.2]⟩

theorem j1_source_mem_nearbyIdx {K : ℕ} {δ : ℝ}
    {b : ℤ × ℤ} (hb : j1SourceSquarePred K δ b)
    (hδ : δ ≤ 1 / 4) : b ∈ j1NearbyIdx K := by
  classical
  obtain ⟨z, hz, hdist⟩ := j1_source_center_near_square hb
  have hxy : ‖z - T20.dyCenter K b‖ < 2 * (1 / 4) := by
    rw [← dist_eq_norm, dist_comm]
    linarith
  obtain ⟨b', hb', hc'⟩ := T20B.exists_nearIdx K hz hxy
  have hc := j1_center_mem_hoBlock K b
  simp only [T20B.hoBlock, Set.mem_ofPred_eq] at hc hc'
  have hbb : b = b' := Prod.ext (hc.1.symm.trans hc'.1) (hc.2.symm.trans hc'.2)
  rw [j1NearbyIdx, Finset.mem_filter]
  exact ⟨hbb ▸ hb', j1_source_center_nearbyBox hb hδ⟩

open Classical in
def j1SourceIdx (K : ℕ) (δ : ℝ) : Finset (ℤ × ℤ) :=
  (j1NearbyIdx K).filter (j1SourceSquarePred K δ)

theorem j1_mem_sourceIdx_iff {K : ℕ} {δ : ℝ} {b : ℤ × ℤ}
    (hδ : δ ≤ 1 / 4) :
    b ∈ j1SourceIdx K δ ↔ j1SourceSquarePred K δ b := by
  classical
  simp only [j1SourceIdx, Finset.mem_filter]
  exact ⟨And.right, fun hb => ⟨j1_source_mem_nearbyIdx hb hδ, hb⟩⟩

theorem j1_sourceIdx_subset_nearbyIdx (K : ℕ) (δ : ℝ) :
    j1SourceIdx K δ ⊆ j1NearbyIdx K := by
  classical
  exact Finset.filter_subset _ _

theorem j1_source_union_le_nearby_union
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (K : ℕ) (δ : ℝ) (E : ℤ × ℤ → Set Ω) :
    P {ω | ∃ b ∈ j1SourceIdx K δ, ω ∈ E b} ≤
      P {ω | ∃ b ∈ j1NearbyIdx K, ω ∈ E b} :=
  MeasureTheory.measure_mono (by
    rintro ω ⟨b, hb, hω⟩
    exact ⟨b, j1_sourceIdx_subset_nearbyIdx K δ hb, hω⟩)

end SupercriticalLQGUniqueness.B2.DG20Conc
