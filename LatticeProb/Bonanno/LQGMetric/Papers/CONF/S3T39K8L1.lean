/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K8L1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.TopoOrdCara
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eArcs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoJaniszewski

/-!
# `T39K8LocAccessI`, part 1: the unbounded complementary component of a Jordan-bounded set

For `K` closed and bounded with `∂K` a Jordan curve, and `W` the unbounded component of `ℂ ∖ K`,
`∂W = ∂K` (**`k8l_frontier_cc`**). Inclusion `∂W ⊆ ∂K` is elementary. For `∂K ⊆ ∂W`: if
`p ∈ ∂K` had a ball `B(p, r)` disjoint from `W`, the arc `A ⊆ ∂K` obtained by removing from `∂K`
a small open subarc around `p` (`k8l_jordan_arc`) does not separate the plane
(`k8l_arc_not_sep`: QuantumZipper `CA.Topo.hasLogOn_of_arc` + `not_separates_of_hasLogOn`,
Burckel, *Classical Analysis in the Complex Plane* (2021), Ex. 4.37(i) and T4(b)), so the
component of `ℂ ∖ A` containing `p` reaches `W` and meets `∂W ⊆ ∂K ∖ A ⊆ B(p, r)`: contradiction.
This is the standard argument that every point of a Jordan curve is a boundary point of each
complementary component (Newman, *Elements of the Topology of Plane Sets of Points*, Ch. V),
specialized to the unbounded component, where no Jordan separation theorem is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter

namespace LQGMetric.CONF

/-- **an arc does not separate the plane** (QuantumZipper T4(b)) -/
theorem k8l_arc_not_sep {g : ℝ → ℂ} (hg : ContinuousOn g (Icc 0 1)) (hinj : InjOn g (Icc 0 1))
    {a b : ℂ} (ha : a ∉ g '' Icc 0 1) (hb : b ∉ g '' Icc 0 1) :
    b ∈ connectedComponentIn (g '' Icc 0 1)ᶜ a := by
  refine QuantumZipper.CA.Topo.not_separates_of_hasLogOn (isCompact_Icc.image_of_continuousOn hg)
    ha hb (QuantumZipper.CA.Topo.hasLogOn_of_arc hg hinj ?_ ?_)
  · refine (continuousOn_id.sub continuousOn_const).div (continuousOn_id.sub continuousOn_const) ?_
    intro z hz e
    exact hb (sub_eq_zero.1 e ▸ hz)
  · intro z hz
    refine div_ne_zero (fun e => ha (sub_eq_zero.1 e ▸ hz)) (fun e => hb (sub_eq_zero.1 e ▸ hz))

/-- removing a small open subarc around `p` from a Jordan curve leaves an arc -/
theorem k8l_jordan_arc {γ : ℂ → ℂ} (hγc : ContinuousOn γ (sphere 0 1))
    (hγi : InjOn γ (sphere 0 1)) {p : ℂ} (hp : p ∈ γ '' sphere 0 1) {r : ℝ} (hr : 0 < r) :
    ∃ g : ℝ → ℂ, ContinuousOn g (Icc 0 1) ∧ InjOn g (Icc 0 1) ∧
      g '' Icc 0 1 ⊆ γ '' sphere 0 1 ∧ p ∉ g '' Icc 0 1 ∧
      γ '' sphere 0 1 \ g '' Icc 0 1 ⊆ ball p r := by
  obtain ⟨ζ, hζ, rfl⟩ := hp
  obtain ⟨t₁, rfl⟩ := GM.p412eC_surj hζ
  set h : ℝ → ℂ := γ ∘ GM.p412eC with hh
  have hS : ∀ s, GM.p412eC s ∈ sphere (0 : ℂ) 1 := GM.p412eC_mem
  have hhc : Continuous h := hγc.comp_continuous GM.p412eC_continuous hS
  obtain ⟨η, hη, hηb⟩ := Metric.continuous_iff.1 hhc t₁ r hr
  set e : ℝ := min (η / 2) (1 / 4) with he
  have he0 : 0 < e := by positivity
  have heη : e < η := by have := min_le_left (η / 2) (1 / 4); linarith
  have he4 : e ≤ 1 / 4 := min_le_right _ _
  set g : ℝ → ℂ := fun t => h (t₁ + e + t * (1 - 2 * e)) with hg
  have hgc : Continuous g := hhc.comp (by fun_prop)
  have hpar : ∀ t ∈ Icc (0 : ℝ) 1, t₁ + e + t * (1 - 2 * e) ∈ Icc (t₁ + e) (t₁ + 1 - e) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2]
  have hIcc : ∀ s ∈ Icc (t₁ + e) (t₁ + 1 - e), s ∈ Icc t₁ (t₁ + 1) := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- equal values of `h` on the period force equal parameters away from the endpoints
  have hval : ∀ s ∈ Icc (t₁ + e) (t₁ + 1 - e), ∀ s' ∈ Icc t₁ (t₁ + 1), h s = h s' →
      s = s' := by
    intro s hs s' hs' hss
    rcases GM.p412eC_inj (hIcc s hs) hs' (hγi (hS s) (hS s') hss) with h1 | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · linarith [hs.1]
    · linarith [hs.2]
  refine ⟨g, hgc.continuousOn, ?_, ?_, ?_, ?_⟩
  · intro s hs s' hs' hss
    have := hval _ (hpar s hs) _ (hIcc _ (hpar s' hs')) hss
    have h2 : (s - s') * (1 - 2 * e) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · linarith
    · linarith
  · rintro _ ⟨t, -, rfl⟩
    exact ⟨_, hS _, rfl⟩
  · rintro ⟨t, ht, hte⟩
    have := hval _ (hpar t ht) t₁ ⟨le_rfl, by linarith⟩ hte
    linarith [(hpar t ht).1]
  · rintro _ ⟨⟨ζ', hζ', rfl⟩, hnot⟩
    rw [← GM.p412eC_image_Icc t₁] at hζ'
    obtain ⟨s, hs, rfl⟩ := hζ'
    rw [mem_ball]
    by_cases h1 : s < t₁ + e
    · have := hηb s (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1])
      exact this
    by_cases h2 : t₁ + 1 - e < s
    · have hc : GM.p412eC s = GM.p412eC (s + ((-1 : ℤ) : ℝ)) := (GM.p412eC_add_int s (-1)).symm
      have := hηb (s + ((-1 : ℤ) : ℝ)) (by
        push_cast; rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.2])
      simpa [hh, hc] using this
    · exfalso
      push_neg at h1 h2
      refine hnot ⟨(s - t₁ - e) / (1 - 2 * e), ⟨?_, ?_⟩, ?_⟩
      · exact div_nonneg (by linarith) (by linarith)
      · rw [div_le_one (by linarith)]; linarith
      · simp only [hg, hh, Function.comp]
        have hne : (1 - 2 * e) ≠ 0 := by linarith
        congr 2
        rw [div_mul_cancel₀ _ hne]
        ring

/-- `∂W ⊆ ∂K` for a component `W` of `ℂ ∖ K`, `K` closed -/
theorem k8l_frontier_cc_subset {K : Set ℂ} (hK : IsClosed K) (p₀ : ℂ) :
    frontier (connectedComponentIn Kᶜ p₀) ⊆ frontier K := by
  set W := connectedComponentIn Kᶜ p₀
  have hWo : IsOpen W := hK.isOpen_compl.connectedComponentIn
  intro q hq
  have hqW : q ∉ W := fun h => hq.2 (hWo.interior_eq.symm ▸ h)
  have hqK : q ∈ K := by
    by_contra hqK
    obtain ⟨ρ, hρ, hρK⟩ := Metric.isOpen_iff.1 hK.isOpen_compl q hqK
    obtain ⟨v, hv1, hv2⟩ := Metric.mem_closure_iff.1 hq.1 ρ hρ
    have hsub : ball q ρ ⊆ connectedComponentIn Kᶜ v :=
      (convex_ball q ρ).isPreconnected.subset_connectedComponentIn
        (mem_ball_comm.1 (mem_ball.2 hv2)) hρK
    rw [← connectedComponentIn_eq hv1] at hsub
    exact hqW (hsub (mem_ball_self hρ))
  rw [hK.frontier_eq]
  refine ⟨hqK, fun hqi => ?_⟩
  obtain ⟨v, hv1, hv2⟩ := mem_closure_iff.1 hq.1 _ isOpen_interior hqi
  exact connectedComponentIn_subset _ _ hv2 (interior_subset hv1)

/-- **`∂W = ∂K`** for the unbounded component `W` of `ℂ ∖ K`, `∂K` a Jordan curve -/
theorem k8l_frontier_cc {K : Set ℂ} (hK : IsClosed K)
    (hJor : JordanMap.IsJordanCurve (frontier K)) {R : ℝ} (hR : K ⊆ ball 0 R) {p₀ : ℂ}
    (hp₀ : R < ‖p₀‖) : frontier (connectedComponentIn Kᶜ p₀) = frontier K := by
  set W := connectedComponentIn Kᶜ p₀
  have hWo : IsOpen W := hK.isOpen_compl.connectedComponentIn
  refine subset_antisymm (k8l_frontier_cc_subset hK p₀) fun p hp => ?_
  by_contra hpW
  have hpK : p ∈ K := hK.frontier_eq ▸ hp |>.1
  have hpW' : p ∉ W := fun h => connectedComponentIn_subset _ _ h hpK
  have hpcl : p ∉ closure W := fun h => hpW ⟨h, hWo.interior_eq.symm ▸ hpW'⟩
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl p hpcl
  obtain ⟨γ, hγc, hγi, hγe⟩ := hJor
  rw [← hγe] at hp
  obtain ⟨g, hgc, hgi, hgC, hpg, hCg⟩ := k8l_jordan_arc hγc hγi hp hr
  rw [hγe] at hgC hCg
  have hp₀K : p₀ ∉ K := fun h => by
    have := hR h; rw [mem_ball_zero_iff] at this; linarith
  have hp₀W : p₀ ∈ W := mem_connectedComponentIn hp₀K
  have hp₀g : p₀ ∉ g '' Icc 0 1 := fun h =>
    hp₀K ((hgC.trans (frontier_subset_closure.trans hK.closure_eq.subset)) h)
  have hmem := k8l_arc_not_sep hgc hgi hpg hp₀g
  obtain ⟨q, hqV, hqF⟩ := GM.jb_inter_frontier_nonempty hWo.isClosed_compl
    (isPreconnected_connectedComponentIn (F := (g '' Icc 0 1)ᶜ) (x := p)) hmem
    (fun h => h hp₀W) (mem_connectedComponentIn (fun h => hpg h)) hpW'
  rw [frontier_compl] at hqF
  have hqg : q ∉ g '' Icc 0 1 := connectedComponentIn_subset _ _ hqV
  have hqb : q ∈ ball p r := hCg ⟨k8l_frontier_cc_subset hK p₀ hqF, hqg⟩
  obtain ⟨v, hv1, hv2⟩ := mem_closure_iff.1 hqF.1 _ isOpen_ball hqb
  exact hrW hv1 (subset_closure hv2)

end LQGMetric.CONF
