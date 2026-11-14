/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.PathHit at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SLUMetricAPI
import LatticeProb.Bonanno.LQGMetric.Metric.CurveLength
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Analysis.Convex.PathConnected




 
set_option autoImplicit false
noncomputable section
open Set Metric
namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation


namespace LSCMetric


theorem eq_of_euclidean_and_metric_limits (D : LSCMetric) {u : ℕ → ℂ} {w x : ℂ}
    (hw : Filter.Tendsto u Filter.atTop (nhds w))
    (hd : Filter.Tendsto (fun n => (D.pt (u n))) Filter.atTop (nhds (D.pt x))) : w = x := by
  have hd0 : Filter.Tendsto (fun n => D (u n, x)) Filter.atTop (nhds 0) := by
    exact (tendsto_iff_edist_tendsto_0).mp hd
  have hpair : Filter.Tendsto (fun n => ((u n, x), D (u n, x))) Filter.atTop
      (nhds ((w, x), (0 : ENNReal))) := (hw.prodMk_nhds tendsto_const_nhds).prodMk_nhds hd0
  have hle : D (w, x) ≤ 0 :=
    D.lowerSemicontinuous.isClosed_epigraph.mem_of_tendsto hpair
      (Filter.Eventually.of_forall fun n => (show D (u n, x) ≤ D (u n, x) from le_rfl))
  exact D.isExtMetric.2.1 w x (le_zero_iff.mp hle)


theorem continuousOn_euclidean_of_bounded (D : LSCMetric) (P : ℝ → ℂ) {a b : ℝ}
    (hP : D.IsCurve P a b) (hbounded : Bornology.IsBounded (P '' Icc a b)) :
    ContinuousOn P (Icc a b) := by
  obtain ⟨R, hR⟩ := hbounded.subset_ball 0
  intro t ht
  change Filter.Tendsto P (nhdsWithin t (Icc a b)) (nhds (P t))
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hseq : ∀ᶠ n in Filter.atTop, P (ns n) ∈ Metric.closedBall 0 R := by
    filter_upwards [hns.eventually (self_mem_nhdsWithin)] with n hn
    exact Metric.ball_subset_closedBall (hR ⟨ns n, hn, rfl⟩)
  obtain ⟨w, hwK, φ, hφ, hw⟩ :=
    (isCompact_closedBall (0 : ℂ) R).tendsto_subseq' hseq.frequently
  refine ⟨φ, ?_⟩
  have hnsφ : Filter.Tendsto (ns ∘ φ) Filter.atTop (nhdsWithin t (Icc a b)) :=
    hns.comp hφ.tendsto_atTop
  have hD : Filter.Tendsto (fun n => D.pt (P (ns (φ n)))) Filter.atTop
      (nhds (D.pt (P t))) := by
    have hDwithin : Filter.Tendsto (D.pt ∘ P) (nhdsWithin t (Icc a b))
        (nhds (D.pt (P t))) := hP.2 t ht
    exact hDwithin.comp hnsφ
  have hweq : w = P t := LSCMetric.eq_of_euclidean_and_metric_limits D hw hD
  change Filter.Tendsto (fun n => P (ns (φ n))) Filter.atTop (nhds w) at hw
  simpa only [hweq] using hw


end LSCMetric

 
theorem crossing_extract {P : ℝ → ℂ} {a b r R : ℝ} {z : ℂ}
    (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    (hrR : r < R) (ha : dist (P a) z < r) (hb : R < dist (P b) z) :
    ∃ σ τ : ℝ, a ≤ σ ∧ σ < τ ∧ τ ≤ b ∧ dist (P σ) z = r ∧
      dist (P τ) z = R ∧ ∀ u ∈ Icc σ τ, dist (P u) z ∈ Icc r R := by
  have hf : ContinuousOn (fun t => dist (P t) z) (Icc a b) := continuous_dist.comp_continuousOn (hP.prodMk continuousOn_const)
  obtain ⟨σ, τ, hασ, hστ, hτβ, hσ, hτ, hbetween⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hab hf hrR.le ha.le hb.le
  refine ⟨σ, τ, hασ, ?_, hτβ, hσ, hτ, hbetween⟩
  exact lt_of_le_of_ne hστ (by
    intro heq
    have : r = R := by rw [← hσ, ← hτ, heq]
    exact hrR.ne this)

theorem candidate_disconnects_implies_path_hit {K E F : Set ℂ}
    (h : SupercriticalLQGUniqueness.Disconnects K E F) :
    LQGMetric.Disconnects K E F := by
  intro x y γ hx hy
  by_contra hno
  apply h
  refine ⟨Set.range γ, isPreconnected_range γ.continuous, ?_, ?_, ?_⟩
  · intro z hz hzK
    exact hno ⟨z, hz, hzK⟩
  · exact ⟨x, Path.source_mem_range γ, hx⟩
  · exact ⟨y, Path.target_mem_range γ, hy⟩

theorem preconnected_subset_component_of_meets {K S : Set ℂ} {x : ℂ}
    (hS : IsPreconnected S) (hSK : S ⊆ Kᶜ)
    (hmeet : (S ∩ connectedComponentIn Kᶜ x).Nonempty) :
    S ⊆ connectedComponentIn Kᶜ x := by
  obtain ⟨z, hzS, hzV⟩ := hmeet
  have hsub := hS.subset_connectedComponentIn hzS hSK
  rw [connectedComponentIn_eq hzV]
  exact hsub

theorem not_mem_component_of_disconnects {K E F : Set ℂ} {x y : ℂ}
    (hK : IsClosed K) (h : LQGMetric.Disconnects K E F)
    (hx : x ∈ E) (hy : y ∈ F) : y ∉ connectedComponentIn Kᶜ x := by
  intro hyV
  have hxV : x ∈ connectedComponentIn Kᶜ x := by
    have hxK : x ∉ K := connectedComponentIn_nonempty_iff.mp ⟨y, hyV⟩
    exact mem_connectedComponentIn hxK
  have hVo : IsOpen (connectedComponentIn Kᶜ x) := hK.isOpen_compl.connectedComponentIn
  have hVc : IsConnected (connectedComponentIn Kᶜ x) :=
    isConnected_connectedComponentIn_iff.mpr (connectedComponentIn_subset _ _ hxV)
  have hpath := ((hVo.isConnected_iff_isPathConnected).mp hVc).joinedIn x hxV y hyV
  obtain ⟨z, hzγ, hzK⟩ := h x y hpath.somePath hx hy
  obtain ⟨t, rfl⟩ := hzγ
  exact (connectedComponentIn_subset _ _ (hpath.somePath_mem t)) hzK

 

theorem disconnects_meets_pathConnected_crossing {K X : Set ℂ} {z : ℂ} {r R : ℝ}
    (hrR : r ≤ R) (hK : LQGMetric.Disconnects K (Metric.sphere z r) (Metric.sphere z R))
    (hX : IsPathConnected X)
    (hin : (X ∩ Metric.closedBall z r).Nonempty)
    (hout : (X ∩ (Metric.ball z R)ᶜ).Nonempty) : (K ∩ X).Nonempty := by
  obtain ⟨x, hxX, hxr⟩ := hin
  obtain ⟨y, hyX, hyR⟩ := hout
  let γ := (hX.joinedIn x hxX y hyX).somePath
  have hγX : Set.range γ ⊆ X := by
    rintro w ⟨t, rfl⟩
    exact (hX.joinedIn x hxX y hyX).somePath_mem t
  obtain ⟨w, hwγ, hwK⟩ :=
    (LQGMetric.Disconnects.closedBall_compl_ball hrR
      (hK)) x y γ hxr hyR
  exact ⟨w, hwK, hγX hwγ⟩

end SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation
