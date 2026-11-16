import LatticeProb.Topology.ParameterGapBracketing
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # Gaps of directed intersections -/

set_option autoImplicit false

namespace LatticeProb

/-- Equal images of gap endpoints pass to a downward-directed intersection of
closed subsets of the real line. -/
theorem equal_of_gap_iInter {ι Y : Type*} [Nonempty ι] [MetricSpace Y]
    (K : ι → Set ℝ) (f : ℝ → Y) (hclosed : ∀ i, IsClosed (K i))
    (hdir : Directed (· ⊇ ·) K)
    (hgap : ∀ (i : ι) (u : ℝ), u ∈ K i → ∀ v ∈ K i, u < v →
      (∀ w ∈ K i, ¬ (u < w ∧ w < v)) → f u = f v)
    {u v : ℝ} (hu : u ∈ ⋂ i, K i) (hv : v ∈ ⋂ i, K i)
    (huv : u < v) (hbetween : ∀ w ∈ ⋂ i, K i, ¬ (u < w ∧ w < v))
    (hcontu : ContinuousAt f u) (hcontv : ContinuousAt f v) : f u = f v := by
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨δu, hδu, hfu⟩ := Metric.continuousAt_iff.mp hcontu (ε / 2) (by linarith)
  obtain ⟨δv, hδv, hfv⟩ := Metric.continuousAt_iff.mp hcontv (ε / 2) (by linarith)
  let η : ℝ := min (min δu δv) ((v - u) / 3) / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηu : η < δu := by
    have h := min_le_left (min δu δv) ((v - u) / 3)
    have h' := min_le_left δu δv
    dsimp [η]; linarith
  have hηv : η < δv := by
    have h := min_le_left (min δu δv) ((v - u) / 3)
    have h' := min_le_right δu δv
    dsimp [η]; linarith
  have hηuv : 3 * η < v - u := by
    have h := min_le_right (min δu δv) ((v - u) / 3)
    dsimp [η]; linarith
  have hdis : Disjoint (Set.Icc (u + η) (v - η)) (⋂ i, K i) := by
    apply Set.disjoint_left.mpr
    intro w hw hwi
    exact hbetween w hwi (by constructor <;> linarith [hw.1, hw.2])
  obtain ⟨i, hi⟩ := isCompact_Icc.elim_directed_family_closed K hclosed hdis hdir
  have hui : u ∈ K i := Set.mem_iInter.mp hu i
  have hvi : v ∈ K i := Set.mem_iInter.mp hv i
  obtain ⟨s, hs, t, ht, hus, hsx, hyt, htv, hst⟩ :=
    exists_gap_bracketing_interval (K i) (hclosed i) hui hvi (by linarith)
      (by linarith) (by linarith) hi.symm
  have heq : f s = f t := hgap i s hs t ht (by linarith) hst
  have hsu : dist s u < δu := by
    rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ s - u)]
    linarith
  have htv' : dist t v < δv := by
    rw [Real.dist_eq, abs_of_nonpos (by linarith : t - v ≤ 0)]
    linarith
  have h₁ := hfu hsu
  have h₂ := hfv htv'
  rw [heq] at h₁
  have htri := dist_triangle (f u) (f s) (f v)
  rw [heq, dist_comm (f u) (f t)] at htri
  linarith

end LatticeProb
