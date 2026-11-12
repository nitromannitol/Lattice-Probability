/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_5ProofBDet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5ProofBSp
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.5 B, deterministic part: internal metrics of the limits

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:1018 apply Lemma 2.11 to get
`D_{h,W}(·,·;W) = D_h(·,·;W)`. The proof of Lemma 2.11 (T:980–988, formalized as
`ContMetric.internal_eq_of_tendsto_internal_closure`) has two steps: (a) near each `z ∈ W`, the
limits agree, `D̃ = D` (T:982–986: for `D(u,v) < D(u,∂W)` both are limits of
`Dⁿ(u,v) = Dⁿ(u,v;W̄)`); (b) a local isometry preserves internal metrics (T:986–988). We keep (b)
verbatim (`internal_eq_of_locally_eq`, the proof of `internal_eq_of_tendsto_internal_closure`
from its local agreement step on) and obtain (a) from two closed conditions that pass to
subsequential limits in law (`dyC1`, `dyC2`): `D ≤ D̃` on `W̄`, and `D̃(u,v) ≤ D(u,v)` whenever
`D(u,v) < D(u,w)` for all `w ∈ ∂W̄` (the same inequalities as in T:982–984).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint MetricGeometry LFPP

/-- **DFGPS T:986–988** (last step of Lemma 2.11): local agreement of `D̃` with `D` near each
point of `V` gives equality of the internal metrics on `V`. -/
theorem internal_eq_of_locally_eq (D : ContMetric) {V : Set ℂ} (dt : closure V × closure V → ℝ)
    (hdt : IsMetricFun dt)
    (hc : Continuous (MetricFunSpace.pt dt hdt)) (hc' : Continuous (metricFunSpaceVal dt hdt))
    (hloc : ∀ z ∈ V, ∃ r > 0, ∀ u v : closure V, u.1 ∈ ball z r → v.1 ∈ ball z r →
      dt (u, v) = D.1 (u.1, v.1))
    (u v : closure V) (hu : u.1 ∈ V) (hv : v.1 ∈ V) :
    D.internal V u v = internalEDist {x : MetricFunSpace dt hdt | (metricFunSpaceVal dt hdt x).1 ∈ V}
      (MetricFunSpace.pt dt hdt u) (MetricFunSpace.pt dt hdt v) := by
  set Y₁ : Set D.Space := {x | D.unpt x ∈ V} with hY₁def
  set Y₂ : Set (MetricFunSpace dt hdt) := {x | (metricFunSpaceVal dt hdt x).1 ∈ V}
  have hY₁ : D.pt '' V = Y₁ := Set.ext fun x => D.mem_image_pt (z := D.unpt x)
  let e : Y₁ ≃ₜ Y₂ :=
    { toFun := fun x => ⟨MetricFunSpace.pt dt hdt ⟨D.unpt x.1, subset_closure x.2⟩, x.2⟩
      invFun := fun y => ⟨D.pt (metricFunSpaceVal dt hdt y.1).1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun :=
        (hc.comp ((D.continuous_unpt.comp continuous_subtype_val).subtype_mk _)).subtype_mk _
      continuous_invFun := (D.continuous_pt.comp (continuous_subtype_val.comp
        (hc'.comp continuous_subtype_val))).subtype_mk _ }
  have he : IsLocalIsometryOn e := by
    intro z'
    obtain ⟨r, hr, hloc'⟩ := hloc _ z'.2
    refine ⟨{x : Y₁ | D.unpt x.1 ∈ ball (D.unpt z'.1) r},
      (D.continuous_unpt.comp continuous_subtype_val).continuousAt.preimage_mem_nhds
        (ball_mem_nhds _ hr), fun a ha b hb => ?_⟩
    rw [edist_dist, edist_dist]
    congr 1
    exact hloc' ⟨D.unpt a.1, subset_closure a.2⟩ ⟨D.unpt b.1, subset_closure b.2⟩ ha hb
  have := internalEDist_eq_of_isLocalIsometryOn he ⟨D.pt u.1, hu⟩ ⟨D.pt v.1, hv⟩
  rw [ContMetric.internal, hY₁]
  exact this.symm

/-- `q.1 ≤ q.2` on `K × K` -/
def c1Set (K : Set ℂ) : Set (C(K × K, ℝ) × C(K × K, ℝ)) := {q | ∀ u v : K, q.1 (u, v) ≤ q.2 (u, v)}

/-- `q.2(u,v) ≤ q.1(u,v)` whenever `q.1(u,v) < q.1(u,w)` for all `w ∈ ∂K` -/
def c2Set (K : Set ℂ) : Set (C(K × K, ℝ) × C(K × K, ℝ)) :=
  {q | ∀ u v : K, (∀ w : K, w.1 ∈ frontier K → q.1 (u, v) < q.1 (u, w)) → q.2 (u, v) ≤ q.1 (u, v)}

theorem isClosed_c1Set (K : Set ℂ) : IsClosed (c1Set K) := by
  have e : c1Set K = ⋂ u : K, ⋂ v : K,
      {q : C(K × K, ℝ) × C(K × K, ℝ) | q.1 (u, v) ≤ q.2 (u, v)} := by
    ext q; simp [c1Set]
  rw [e]
  exact isClosed_iInter fun u => isClosed_iInter fun v =>
    isClosed_le ((continuous_eval_const _).comp continuous_fst)
      ((continuous_eval_const _).comp continuous_snd)

theorem isClosed_c2Set {K : Set ℂ} [CompactSpace K] : IsClosed (c2Set K) := by
  refine isClosed_of_closure_subset fun q hq => ?_
  obtain ⟨qn, hqn, hlim⟩ := mem_closure_iff_seq_limit.1 hq
  intro u v hw
  have h1 : Tendsto (fun n => (qn n).1) atTop (𝓝 q.1) := (continuous_fst.tendsto q).comp hlim
  have h2 : Tendsto (fun n => (qn n).2) atTop (𝓝 q.2) := (continuous_snd.tendsto q).comp hlim
  set F : Set K := {w | w.1 ∈ frontier K}
  have hev : ∀ᶠ n in atTop, ∀ w : K, w.1 ∈ frontier K → (qn n).1 (u, v) < (qn n).1 (u, w) := by
    have hFc : IsCompact F := (isClosed_frontier.preimage continuous_subtype_val).isCompact
    rcases F.eq_empty_or_nonempty with he | hne
    · exact Eventually.of_forall fun n w hwf =>
        absurd (show w ∈ F from hwf) (by rw [he]; exact id)
    · obtain ⟨w0, hw0, hmin⟩ := hFc.exists_isMinOn hne (f := fun w => q.1 (u, w))
        (q.1.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
      have hm : 0 < q.1 (u, w0) - q.1 (u, v) := sub_pos.2 (hw w0 hw0)
      filter_upwards [Metric.tendsto_nhds.1 h1 _ (half_pos hm)] with n hn w hwf
      have e1 := (ContinuousMap.dist_apply_le_dist (f := (qn n).1) (g := q.1) (u, v)).trans_lt hn
      have e2 := (ContinuousMap.dist_apply_le_dist (f := (qn n).1) (g := q.1) (u, w)).trans_lt hn
      rw [Real.dist_eq, abs_lt] at e1 e2
      have := hmin (show w ∈ F from hwf)
      simp only [mem_ofPred_eq] at this
      linarith [e1.1, e1.2, e2.1, e2.2]
  exact le_of_tendsto_of_tendsto (((continuous_eval_const (u, v)).tendsto q.2).comp h2)
    (((continuous_eval_const (u, v)).tendsto q.1).comp h1)
    (hev.mono fun n hn => hqn n u v hn)

/-- the pair `(D|_{W̄²}, D_W)` -/
def dyPair (W : dyadicDomainsC) (x : DyProd) :
    C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ) × C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ) :=
  (restrSq (closure (W : Set ℂ)) x.1, x.2 W)

theorem continuous_dyPair (W : dyadicDomainsC) : Continuous (dyPair W) :=
  ((restrSq _).continuous.comp continuous_dyProd_fst).prodMk (continuous_dyProd_snd W)

/-- the closed condition `D ≤ D_W` on `W̄` -/
def dyC1 (W : dyadicDomainsC) : Set DyProd := dyPair W ⁻¹' c1Set (closure (W : Set ℂ))

/-- the closed condition `D_W(u,v) ≤ D(u,v)` if `D(u,v) < D(u, ∂W̄)` -/
def dyC2 (W : dyadicDomainsC) : Set DyProd := dyPair W ⁻¹' c2Set (closure (W : Set ℂ))

theorem isClosed_dyC1 (W : dyadicDomainsC) : IsClosed (dyC1 W) :=
  (isClosed_c1Set _).preimage (continuous_dyPair W)

theorem isClosed_dyC2 (W : dyadicDomainsC) : IsClosed (dyC2 W) :=
  isClosed_c2Set.preimage (continuous_dyPair W)

theorem continuous_metricFunSpace_pt {K : Type*} [TopologicalSpace K] {d : C(K × K, ℝ)}
    (hd : IsMetricFun ⇑d) : Continuous (MetricFunSpace.pt (⇑d) hd) := by
  rw [Metric.continuous_iff']
  intro a ε hε
  have ht : Tendsto (fun x => d (x, a)) (𝓝 a) (𝓝 (d (a, a))) :=
    (d.continuous.comp (continuous_id.prodMk continuous_const)).tendsto a
  rw [hd.self_eq_zero] at ht
  exact ht.eventually (gt_mem_nhds hε)

/-- **DFGPS T:1016–1018, deterministic part**: the limit object is an `IsDyadicLimit`. -/
theorem isDyadicLimit_of {x : DyProd} (h1 : IsContLengthMetric x.1)
    (h2 : ∀ W, IsSqLengthMetric (x.2 W)) (h3 : ∀ W, x ∈ dyC1 W) (h4 : ∀ W, x ∈ dyC2 W) :
    IsDyadicLimit x := by
  refine ⟨h1, fun W => ?_⟩
  obtain ⟨hd, hlen⟩ := h2 W
  have hpt := continuous_metricFunSpace_pt hd
  let H : closure (W : Set ℂ) ≃ₜ MetricFunSpace (⇑(x.2 W)) hd :=
    Continuous.homeoOfEquivCompactToT2
      (f := (Equiv.refl _ : closure (W : Set ℂ) ≃ MetricFunSpace (⇑(x.2 W)) hd)) hpt
  have hval : Continuous (metricFunSpaceVal (⇑(x.2 W)) hd) := H.symm.continuous
  refine ⟨hd, hlen, hpt, hval, fun hc u v hu hv => ?_⟩
  set D : ContMetric := ⟨x.1, hc⟩
  have hWo : IsOpen (W : Set ℂ) := W.2.1.isOpen
  have hWc : IsCompact (closure (W : Set ℂ)) := isCompact_closure_dyadicDomainsC W
  refine internal_eq_of_locally_eq D (x.2 W) hd hpt hval (fun z hz => ?_) u v hu hv
  have hC1 : ∀ a b : closure (W : Set ℂ), x.1 (a.1, b.1) ≤ x.2 W (a, b) := h3 W
  have hC2 : ∀ a b : closure (W : Set ℂ),
      (∀ w : closure (W : Set ℂ), w.1 ∈ frontier (closure (W : Set ℂ)) →
        x.1 (a.1, b.1) < x.1 (a.1, w.1)) → x.2 W (a, b) ≤ x.1 (a.1, b.1) := h4 W
  have hsymm := hc.symm
  have htri := hc.triangle
  set Fr := frontier (closure (W : Set ℂ))
  rcases Fr.eq_empty_or_nonempty with hFe | hFne
  · refine ⟨1, one_pos, fun a b _ _ => le_antisymm (hC2 a b fun w hw => ?_) (hC1 a b)⟩
    rw [hFe] at hw; exact absurd hw id
  have hFc : IsCompact Fr := hWc.of_isClosed_subset isClosed_frontier
    (isClosed_closure.frontier_subset)
  obtain ⟨w0, hw0, hmin⟩ := hFc.exists_isMinOn hFne (f := fun w => x.1 (z, w))
    (x.1.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hzw0 : z ≠ w0 := fun e => by
    have hzi : z ∈ interior (closure (W : Set ℂ)) :=
      interior_mono subset_closure (hWo.interior_eq.symm ▸ hz)
    exact hw0.2 (e ▸ hzi)
  have hρ : 0 < x.1 (z, w0) := by
    have h0 : 0 ≤ x.1 (z, w0) := by
      have := htri z w0 z; rw [hc.self_eq_zero, hsymm w0 z] at this; linarith
    exact lt_of_le_of_ne h0 fun e => hzw0 (hc.eq_of_eq_zero _ _ e.symm)
  set ρ := x.1 (z, w0)
  have hcz : Tendsto (fun a => x.1 (z, a)) (𝓝 z) (𝓝 (x.1 (z, z))) :=
    (x.1.continuous.comp (continuous_const.prodMk continuous_id)).tendsto z
  rw [hc.self_eq_zero] at hcz
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (hcz.eventually (gt_mem_nhds
    (show (0 : ℝ) < ρ / 3 by positivity)))
  refine ⟨r, hr, fun a b ha hb => le_antisymm (hC2 a b fun w hw => ?_) (hC1 a b)⟩
  have hza := hball (show dist a.1 z < r from ha)
  have hzb := hball (show dist b.1 z < r from hb)
  have hmw := hmin hw
  simp only [mem_ofPred_eq] at hmw
  have e1 := htri a.1 z b.1
  have e2 := htri z a.1 w.1
  rw [hsymm a.1 z] at e1
  linarith

end LQGMetric.DFGPS
