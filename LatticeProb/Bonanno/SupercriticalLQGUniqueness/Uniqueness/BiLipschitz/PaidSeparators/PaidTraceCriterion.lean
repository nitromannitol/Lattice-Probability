/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators.PaidTraceCriterion at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators.AcrossLocalization
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.Components
import LatticeProb.Bonanno.LQGMetric.Metric.Geodesic
import Mathlib.Topology.MetricSpace.CoveringNumbers
import LatticeProb.Bonanno.LQGMetric.Metric.InternalOps




 





set_option autoImplicit false
noncomputable section

open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators

 
def sepAnn (x : ℂ) (r : ℝ) (hr : 0 < r) : EuclideanAnnulus :=
  ⟨(x, 2 * r, 3 * r), by linarith, by linarith⟩

 


theorem first_hit_stays_component {K : Set ℂ} (hK : IsClosed K)
    {P : ℝ → ℂ} {s T : ℝ} (hPc : ContinuousOn P (Icc s T))
    (hsT : s ≤ T) (hstart : P s ∉ K)
    (hhit : ∃ u ∈ Icc s T, P u ∈ K) :
    ∃ t ∈ Icc s T, s < t ∧ P t ∈ K ∧
      ∀ u ∈ Ico s t, P u ∈ connectedComponentIn Kᶜ (P s) := by
  obtain ⟨t, ht, htK, hbefore⟩ :=
    LQGMetric.MetricGeometry.exists_first_hit hPc hK hhit
  have hst : s < t := lt_of_le_of_ne ht.1 (by
    intro heq
    have : P s ∈ K := heq ▸ htK
    exact hstart this)
  refine ⟨t, ht, hst, htK, ?_⟩
  intro u hu
  have huT : u ∈ Icc s T := ⟨hu.1, hu.2.le.trans ht.2⟩
  have hsub : Icc s u ⊆ Icc s T := Icc_subset_Icc le_rfl huT.2
  have havoid : P '' Icc s u ⊆ Kᶜ := by
    rintro y ⟨v, hv, rfl⟩
    exact hbefore v ⟨hv.1, hv.2.trans_lt hu.2⟩
  have hconn : IsPreconnected (P '' Icc s u) :=
    (isPreconnected_Icc).image P (hPc.mono hsub)
  have hcomponent : P '' Icc s u ⊆ connectedComponentIn Kᶜ (P s) :=
    hconn.subset_connectedComponentIn
      ⟨s, left_mem_Icc.2 hu.1, rfl⟩ havoid
  exact hcomponent ⟨u, right_mem_Icc.2 hu.1, rfl⟩

 

theorem no_hit_stays_component {K : Set ℂ}
    {P : ℝ → ℂ} {s T : ℝ} (hPc : ContinuousOn P (Icc s T))
    (hsT : s ≤ T)
    (havoid : ∀ u ∈ Icc s T, P u ∉ K) :
    ∀ u ∈ Icc s T, P u ∈ connectedComponentIn Kᶜ (P s) := by
  have htrace : P '' Icc s T ⊆ Kᶜ := by
    rintro y ⟨u, hu, rfl⟩
    exact havoid u hu
  have hconn : IsPreconnected (P '' Icc s T) :=
    (isPreconnected_Icc).image P hPc
  have hcomponent : P '' Icc s T ⊆ connectedComponentIn Kᶜ (P s) :=
    hconn.subset_connectedComponentIn
      ⟨s, left_mem_Icc.2 hsT, rfl⟩ htrace
  intro u hu
  exact hcomponent ⟨u, hu, rfl⟩

 

theorem no_infinite_paid_steps (D : LSCMetric) {P : ℝ → ℂ}
    {T η : ℝ} (hη : 0 < η) (hT : 0 ≤ T)
    (hfin : D.len P 0 T ≠ ∞) (S : ℕ → ℝ)
    (hS0 : S 0 = 0) (hSI : ∀ n, S n ∈ Icc (0 : ℝ) T)
    (hstep : ∀ n, S n ≤ S (n + 1))
    (hcost : ∀ n, ENNReal.ofReal η ≤ D.len P (S n) (S (n + 1))) : False := by
  have hlinear : ∀ n : ℕ,
      ENNReal.ofReal ((n : ℝ) * η) ≤ D.len P 0 (S n) := by
    intro n
    induction n with
    | zero =>
        simpa [hS0, LSCMetric.len] using
          (show (0 : ℝ≥0∞) ≤ D.len P 0 0 from bot_le)
    | succ n ih =>
        have hn : 0 ≤ (n : ℝ) * η := mul_nonneg (Nat.cast_nonneg _) hη.le
        have hrec : ((↑(n + 1) : ℝ) * η) = (n : ℝ) * η + η := by
          push_cast
          ring
        rw [hrec, ENNReal.ofReal_add hn hη.le]
        calc
          ENNReal.ofReal ((n : ℝ) * η) + ENNReal.ofReal η
              ≤ D.len P 0 (S n) + D.len P (S n) (S (n + 1)) :=
                add_le_add ih (hcost n)
          _ = D.len P 0 (S (n + 1)) := by
            exact LQGMetric.MetricGeometry.curveLength_add (D.pt ∘ P)
              (hSI n).1 (hstep n)
  obtain ⟨n, hn⟩ := exists_nat_gt ((D.len P 0 T).toReal / η)
  have hnt : (D.len P 0 T).toReal < (n : ℝ) * η := by
    rwa [div_lt_iff₀ hη] at hn
  have hbound : D.len P 0 (S n) ≤ D.len P 0 T :=
    LQGMetric.MetricGeometry.curveLength_mono (D.pt ∘ P) le_rfl (hSI n).2
  have hcast := ENNReal.toReal_mono hfin ((hlinear n).trans hbound)
  rw [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) hη.le)] at hcast
  exact (not_lt_of_ge hcast) hnt

 

theorem component_pair_close {V : Set ℂ} {x z w : ℂ} {r ε : ℝ}
    (hr : 0 < r) (hrε : r ≤ ε)
    (hV : V ⊆ ball x (3 * r)) (hz : z ∈ V) (hw : w ∈ V) :
    dist z w < 6 * ε := by
  have hz' : dist z x < 3 * r := hV hz
  have hw' : dist w x < 3 * r := hV hw
  calc
    dist z w ≤ dist z x + dist x w := dist_triangle z x w
    _ < 6 * ε := by
      rw [dist_comm x w]
      linarith

 

theorem exists_trace_near_component {K V : Set ℂ} {x z : ℂ}
    {r ε : ℝ} (hr : 0 < r) (hrε : r ≤ ε)
    (hKne : K.Nonempty) (hK : K ⊆ ball x (3 * r))
    (hV : V ⊆ ball x (3 * r)) (hz : z ∈ closure V) :
    ∃ q ∈ K, dist z q < 7 * ε := by
  obtain ⟨q, hq⟩ := hKne
  have hz' : dist z x ≤ 3 * r := by
    have hclosed : closure V ⊆ closedBall x (3 * r) :=
      closure_minimal (hV.trans ball_subset_closedBall) isClosed_closedBall
    exact hclosed hz
  have hq' : dist q x < 3 * r := hK hq
  refine ⟨q, hq, ?_⟩
  calc
    dist z q ≤ dist z x + dist x q := dist_triangle z x q
    _ < 7 * ε := by
      rw [dist_comm x q]
      linarith

 

theorem exists_trace_near_terminal {K V Vlast : Set ℂ} {x xlast p w : ℂ}
    {r rlast ε : ℝ} (hr : 0 < r) (hrlast : 0 < rlast)
    (hrε : r ≤ ε) (hrlastε : rlast ≤ ε)
    (hKne : K.Nonempty) (hK : K ⊆ ball x (3 * r))
    (hV : V ⊆ ball x (3 * r)) (hp : p ∈ closure V)
    (hVlast : Vlast ⊆ ball xlast (3 * rlast))
    (hpLast : p ∈ Vlast) (hwLast : w ∈ Vlast) :
    ∃ q ∈ K, dist w q < 13 * ε := by
  obtain ⟨q, hq, hpq⟩ :=
    exists_trace_near_component hr hrε hKne hK hV hp
  have hpw : dist p w < 6 * ε :=
    component_pair_close hrlast hrlastε hVlast hpLast hwLast
  refine ⟨q, hq, ?_⟩
  calc
    dist w q ≤ dist w p + dist p q := dist_triangle w p q
    _ < 13 * ε := by rw [dist_comm w p]; linarith


end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators
