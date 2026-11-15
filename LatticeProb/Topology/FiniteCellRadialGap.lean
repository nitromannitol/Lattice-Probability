import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Linarith

/-! # Rational radial gaps for locally finite families -/

set_option autoImplicit false

namespace LatticeProb

open Set

/-- If only finitely many nonempty sets meet an outer ball, every nonempty
interval of radii below its radius contains a rational subinterval which
contains none of the distances from the center to the sets. -/
theorem exists_rational_radial_gap_of_finite_inter_ball
    {ι E : Type*} [MetricSpace E] (C : ι → Set E) (hC : ∀ i, (C i).Nonempty)
    (z : E) {a b : ℝ} (hab : a < b)
    (hfin : {i | (C i ∩ Metric.ball z b).Nonempty}.Finite) :
    ∃ p q : ℚ, a < (p : ℝ) ∧ (p : ℝ) < q ∧ (q : ℝ) < b ∧
      ∀ i, Metric.infDist z (C i) ≤ p ∨ (q : ℝ) ≤ Metric.infDist z (C i) := by
  let F : Set ι := {i | (C i ∩ Metric.ball z b).Nonempty}
  let D : Set ℝ := (fun i => Metric.infDist z (C i)) '' F
  have hD : D.Finite := hfin.image _
  have hnot : ¬ Ioo a b ⊆ D := by
    intro hsub
    exact (Set.Ioo_infinite hab) (hD.subset hsub)
  obtain ⟨x, hx, hxD⟩ := Set.not_subset.mp hnot
  have hopen : IsOpen (Ioo a b ∩ Dᶜ) := isOpen_Ioo.inter hD.isClosed.isOpen_compl
  obtain ⟨u, v, huv, huvsub⟩ := hopen.exists_Ioo_subset ⟨x, hx, hxD⟩
  obtain ⟨p, hup, hpv⟩ := exists_rat_btwn huv
  obtain ⟨q, hpq, hqv⟩ := exists_rat_btwn hpv
  have hp : (p : ℝ) ∈ Ioo a b ∩ Dᶜ := huvsub ⟨hup, hpv⟩
  have hq : (q : ℝ) ∈ Ioo a b ∩ Dᶜ := huvsub ⟨lt_trans hup hpq, hqv⟩
  refine ⟨p, q, hp.1.1, hpq, hq.1.2, fun i => ?_⟩
  by_contra hn
  have hpi : (p : ℝ) < Metric.infDist z (C i) := lt_of_not_ge (fun h => hn (Or.inl h))
  have hiq : Metric.infDist z (C i) < (q : ℝ) := lt_of_not_ge (fun h => hn (Or.inr h))
  have hib : Metric.infDist z (C i) < b := lt_trans hiq hq.1.2
  obtain ⟨y, hy, hyd⟩ := (Metric.infDist_lt_iff (hC i)).1 hib
  have hiF : i ∈ F := ⟨y, hy, by simpa only [Metric.mem_ball, dist_comm] using hyd⟩
  have hiD : Metric.infDist z (C i) ∈ D := ⟨i, hiF, rfl⟩
  have hiuv : Metric.infDist z (C i) ∈ Ioo u v := ⟨lt_trans hup hpi, lt_trans hiq hqv⟩
  exact (huvsub hiuv).2 hiD

end LatticeProb
