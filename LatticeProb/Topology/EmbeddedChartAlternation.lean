import LatticeProb.Topology.DiskAlternationComplex
import LatticeProb.Topology.InvertedExteriorDisc
import LatticeProb.Topology.JordanDiskIntersectionBoundary

/-! # Alternating continua under a disk chart -/

open Set Metric Complex LQGMetric

namespace LatticeProb.Topology

/-- Disk-chart alternation holds when the chart is continuous and injective on an
ambient set containing the continua. -/
theorem nonempty_inter_of_alternating_disk_chart_on {X : Type*} [TopologicalSpace X]
    {S : Set X} {g : X → ℂ} (hg : ContinuousOn g S) (hgi : InjOn g S)
    {P Q : Set X} (hPS : P ⊆ S) (hQS : Q ⊆ S)
    (hP : IsCompact P) (hPc : IsConnected P) (hQ : IsCompact Q) (hQc : IsConnected Q)
    (hPD : g '' P ⊆ closedBall (0 : ℂ) 1)
    (hQD : g '' Q ⊆ closedBall (0 : ℂ) 1)
    {θ₁ θ₂ θ₃ θ₄ : ℝ} (h₁₂ : θ₁ < θ₂) (h₂₃ : θ₂ < θ₃)
    (h₃₄ : θ₃ < θ₄) (h₄₁ : θ₄ < θ₁ + 2 * Real.pi)
    (h₁ : exp (θ₁ * I) ∈ g '' P) (h₃ : exp (θ₃ * I) ∈ g '' P)
    (h₂ : exp (θ₂ * I) ∈ g '' Q) (h₄ : exp (θ₄ * I) ∈ g '' Q) :
    (P ∩ Q).Nonempty := by
  have h := nonempty_inter_of_alternating_closedBall (x := (0 : ℂ)) (t := 1)
    (by norm_num) h₁₂ h₂₃ h₃₄ h₄₁ (hP.image_of_continuousOn (hg.mono hPS))
    (hPc.image g (hg.mono hPS)) (hQ.image_of_continuousOn (hg.mono hQS))
    (hQc.image g (hg.mono hQS)) hPD hQD
    (by simpa only [zero_add, Complex.ofReal_one, one_mul] using h₁)
    (by simpa only [zero_add, Complex.ofReal_one, one_mul] using h₃)
    (by simpa only [zero_add, Complex.ofReal_one, one_mul] using h₂)
    (by simpa only [zero_add, Complex.ofReal_one, one_mul] using h₄)
  obtain ⟨z, ⟨p, hp, hpz⟩, ⟨q, hq, hqz⟩⟩ := h
  have hpq : p = q := hgi (hPS hp) (hQS hq) (hpz.trans hqz.symm)
  exact ⟨p, hp, hpq ▸ hq⟩

/-- The closed exterior of a compact Jordan domain has an injective disk chart
which maps its boundary onto the unit circle. -/
theorem exists_closed_exterior_disk_chart {K : Set ℂ} {z : ℂ}
    (hK : IsCompact K) (hz : z ∈ interior K) (hKc : IsPreconnected Kᶜ)
    (hJ : JordanMap.IsJordanCurve (frontier K)) :
    ∃ g : closure Kᶜ → ℂ, Continuous g ∧ Function.Injective g ∧
      (∀ x, g x ∈ closedBall (0 : ℂ) 1) ∧
      g '' {x | (x : ℂ) ∈ frontier K} = sphere 0 1 := by
  obtain ⟨e, _, heB⟩ := LatticeProb.exists_inverted_exterior_disc hK hz hKc hJ
  have hxz : ∀ x : closure Kᶜ, (x : ℂ) ≠ z := by
    intro x h
    have : z ∉ closure Kᶜ := by
      rw [interior_eq_compl_closure_compl] at hz
      exact hz
    exact this (h ▸ x.2)
  have hxinv : ∀ x : closure Kᶜ, ((x : ℂ) - z)⁻¹ ∈
      closure (LQGMetric.CONF.DD.toOmega K z) := by
    intro x
    have hc : ContinuousAt (fun t : ℂ => (t - z)⁻¹) x :=
      (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.2 (hxz x))
    apply closure_mono _ (mem_closure_image hc x.2)
    rw [LQGMetric.CONF.DD.to_omega_eq hz]
    exact subset_union_left
  let F : closure Kᶜ → closure (LQGMetric.CONF.DD.toOmega K z) :=
    fun x => ⟨((x : ℂ) - z)⁻¹, hxinv x⟩
  have hF : Continuous F := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.sub continuous_const).inv₀
      (fun x => sub_ne_zero.2 (hxz x))
  have hFi : Function.Injective F := by
    intro x y hxy
    have h : ((x : ℂ) - z)⁻¹ = ((y : ℂ) - z)⁻¹ := congrArg Subtype.val hxy
    have h' : (x : ℂ) - z = (y : ℂ) - z := inv_injective h
    apply Subtype.ext
    exact sub_left_inj.mp h'
  let g : closure Kᶜ → ℂ := fun x => (e.symm (F x) : ℂ)
  have hg : Continuous g := continuous_subtype_val.comp (e.symm.continuous.comp hF)
  have hgi : Function.Injective g := by
    intro x y hxy
    apply hFi
    apply e.symm.injective
    exact Subtype.ext hxy
  refine ⟨g, hg, hgi, fun x => (e.symm (F x)).property, ?_⟩
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hinv : ((x : ℂ) - z)⁻¹ ∈
        (fun x => (e x : ℂ)) '' {x | (x : ℂ) ∈ sphere 0 1} := by
      rw [heB]
      exact ⟨x, hx, rfl⟩
    obtain ⟨v, hv, hvF⟩ := hinv
    have : e.symm (F x) = v := by
      apply e.injective
      apply Subtype.ext
      simpa only [Homeomorph.apply_symm_apply] using hvF.symm
    change (v : ℂ) ∈ sphere 0 1 at hv
    simpa only [g, this] using hv
  · intro hw
    let v : closedBall (0 : ℂ) 1 := ⟨w, sphere_subset_closedBall hw⟩
    have hv : (e v : ℂ) ∈ (fun x => (x - z)⁻¹) '' frontier K := by
      rw [← heB]
      exact ⟨v, hw, rfl⟩
    obtain ⟨x, hx, hvx⟩ := hv
    have hxcl : x ∈ closure Kᶜ := by
      rw [frontier_eq_closure_inter_closure] at hx
      exact hx.2
    refine ⟨⟨x, hxcl⟩, hx, ?_⟩
    change (e.symm (F ⟨x, hxcl⟩) : ℂ) = w
    have : F ⟨x, hxcl⟩ = e v := Subtype.ext hvx
    rw [this, Homeomorph.symm_apply_apply]

/-- The closed exterior of an embedded disk has an injective chart into the unit
closed disk that maps its boundary onto the unit circle. -/
theorem exists_embedded_disk_exterior_chart {K : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ K) :
    ∃ g : closure Kᶜ → ℂ, Continuous g ∧ Function.Injective g ∧
      (∀ x, g x ∈ closedBall (0 : ℂ) 1) ∧
      g '' {x | (x : ℂ) ∈ frontier K} = sphere 0 1 := by
  have hK : IsCompact K := by
    have h := isCompact_range (continuous_subtype_val.comp e.continuous)
    have hrange : Set.range (fun x => (e x : ℂ)) = K := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact (e y).property
      · intro hx
        exact ⟨e.symm ⟨x, hx⟩, by simp⟩
    change IsCompact (Set.range (fun x => (e x : ℂ))) at h
    rwa [hrange] at h
  let x : closedBall (0 : ℂ) 1 := ⟨0, mem_closedBall_self (by norm_num)⟩
  have hx : (e x : ℂ) ∈ interior K := by
    apply LatticeProb.homeomorph_subspace_mem_interior e x
    rw [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
    exact mem_ball_self (by norm_num)
  exact exists_closed_exterior_disk_chart hK hx
    (LatticeProb.complex_embedded_closed_disk_compl_preconnected_unbounded e).1
    (LatticeProb.isJordanCurve_frontier_of_homeomorph_closedDisk e)

end LatticeProb.Topology
