/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K8L2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K8L1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K8b

/-!
# `T39K8LocAccessI`: local accessibility of a Jordan frontier from the unbounded component

**`t39k8_locAccessI`** proves `T39K8LocAccessI`, i.e. `T39K8LocAccess` (S3T39K8b) for `K` with
nonempty interior (every `K` used is a filled ball with its centre in the interior).

Proof (audit N, row N4; P2-T39K8 handoff): `W` the unbounded component of `ℂ ∖ K`,
`K̂ = ℂ ∖ W ⊇ K`, `z₀ ∈ int K ⊆ int K̂`, `∂K̂ = ∂W = ∂K` (`k8l_frontier_cc`). Inversion
`ι(v) = (v - z₀)⁻¹` maps `W` onto `Ω ∖ {0}` with `Ω = toOmega K̂ z₀` (TopoOrdCara), a bounded
simply connected Jordan domain, and Carathéodory's theorem (`jm_jordan_closedDisc_extension'`;
Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Thm 2.6) gives `f` continuous and
injective on `𝔻̄`, `f(𝔻) = Ω`, `f(∂𝔻) = ι(∂K)`. Points `w ∈ W`, `x' ∈ ∂K` near `x` have
preimages `u₁ ∈ 𝔻`, `u₂ ∈ ∂𝔻` near `u_x = f⁻¹(ιx)` (compactness: `‖f u - ιx‖` has a positive
minimum off `B(u_x, η)`), and `β = ι⁻¹ ∘ f` on the segment `[u₁, u₂]` (inside `𝔻` except at
`u₂`) is the required path (Pommerenke, Prop. 2.3 / Thm 2.6 as cited in S3T39K8b).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter

namespace LQGMetric.CONF

/-- **uniform local accessibility of a Jordan frontier, for `K` with nonempty interior** -/
def T39K8LocAccessI : Prop :=
  ∀ K : Set ℂ, IsClosed K → Bornology.IsBounded K → (interior K).Nonempty →
    JordanMap.IsJordanCurve (frontier K) →
    ∀ x ∈ frontier K, ∀ ε > 0, ∃ δ > 0, ∀ y w : ℂ, JoinedIn Kᶜ y w → (∀ z ∈ K, ‖z‖ < ‖y‖) →
      dist w x < δ → ∀ x' ∈ frontier K, dist x' x < δ →
        ∃ β : Path w x', range β ⊆ ball x ε ∧ range β ∩ K ⊆ {x'}

/-- inversion about `z ∉ Γ` maps Jordan curves to Jordan curves -/
theorem k8l_jordan_inv {Γ : Set ℂ} (hΓ : JordanMap.IsJordanCurve Γ) {z : ℂ} (hz : z ∉ Γ) :
    JordanMap.IsJordanCurve ((fun x => (x - z)⁻¹) '' Γ) := by
  obtain ⟨γ, hγc, hγi, rfl⟩ := hΓ
  have hne : ∀ w ∈ sphere (0 : ℂ) 1, γ w - z ≠ 0 := fun w hw e =>
    hz ⟨w, hw, (sub_eq_zero.1 e)⟩
  refine ⟨fun w => (γ w - z)⁻¹, (hγc.sub continuousOn_const).inv₀ hne, ?_, ?_⟩
  · intro w hw w' hw' h
    exact hγi hw hw' (sub_left_inj.1 (inv_inj.1 h))
  · rw [image_image]

/-- the point `y` beyond `K` lies in the component of `ℂ ∖ K` of a far point `p₀` -/
theorem k8l_mem_cc_far {K : Set ℂ} {R : ℝ} (hR : K ⊆ ball 0 R) {p₀ : ℂ} (hp₀ : R < ‖p₀‖)
    {y : ℂ} (hy : ∀ z ∈ K, ‖z‖ < ‖y‖) (hy0 : y ≠ 0) : y ∈ connectedComponentIn Kᶜ p₀ := by
  set S := (fun t : ℝ => (t : ℂ) * y) '' Ici 1
  have hSp : IsPreconnected S := isPreconnected_Ici.image _ (by fun_prop)
  have hny : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hSn : ∀ t : ℝ, 1 ≤ t → ‖(t : ℂ) * y‖ = t * ‖y‖ := fun t ht => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hSu : ¬ Bornology.IsBounded S := by
    intro hb
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
    have h0 := hC _ ⟨max 1 (C / ‖y‖ + 1), mem_Ici.2 (le_max_left _ _), rfl⟩
    simp only at h0
    rw [hSn _ (le_max_left _ _)] at h0
    have h1 : C / ‖y‖ + 1 ≤ max 1 (C / ‖y‖ + 1) := le_max_right _ _
    have h2 : C / ‖y‖ * ‖y‖ = C := div_mul_cancel₀ _ hny.ne'
    nlinarith
  have hSK : Disjoint S K := by
    rw [Set.disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ hK
    have := hy _ hK
    rw [hSn t ht] at this
    nlinarith [show (1 : ℝ) ≤ t from ht]
  exact QuantumZipper.CA.Topo.subset_connectedComponentIn_compl_of_unbounded hR hSp hSu hSK hp₀
    ⟨1, mem_Ici.2 le_rfl, by simp⟩

/-- a continuous injective map on `𝔻̄` has a uniformly continuous inverse at `f ux` -/
theorem k8l_inv_near {f : ℂ → ℂ} (hfc : ContinuousOn f (closedBall 0 1))
    (hfi : InjOn f (closedBall 0 1)) {ux : ℂ} (hux : ux ∈ closedBall (0 : ℂ) 1) {η : ℝ}
    (hη : 0 < η) : ∃ m > 0, ∀ u ∈ closedBall (0 : ℂ) 1, ‖f u - f ux‖ < m → dist u ux < η := by
  set S := closedBall (0 : ℂ) 1 \ ball ux η
  have hS : IsCompact S := (isCompact_closedBall 0 1).diff isOpen_ball
  rcases S.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun u hu _ => ?_⟩
    by_contra h
    exact (he ▸ (⟨hu, fun h' => h (mem_ball.1 h')⟩ : u ∈ S) : u ∈ (∅ : Set ℂ))
  obtain ⟨u₀, hu₀, hmin⟩ := hS.exists_isMinOn hne
    (((hfc.mono diff_subset).sub continuousOn_const).norm)
  have hpos : 0 < ‖f u₀ - f ux‖ := by
    refine norm_pos_iff.2 fun h => hu₀.2 ?_
    rw [hfi hu₀.1 hux (sub_eq_zero.1 h)]
    exact mem_ball_self hη
  refine ⟨_, hpos, fun u hu hlt => ?_⟩
  by_contra h
  exact (not_le.2 hlt) (hmin (⟨hu, fun h' => h (mem_ball.1 h')⟩ : u ∈ S))

/-- **`T39K8LocAccessI`** (Carathéodory on the exterior of `∂K`) -/
theorem t39k8_locAccessI : T39K8LocAccessI := by
  intro K hK hKb ⟨z₀, hz₀⟩ hJor x hx ε hε
  obtain ⟨R, hR⟩ := hKb.subset_ball (0 : ℂ)
  set p₀ : ℂ := ((|R| + 1 : ℝ) : ℂ) with hp₀def
  have hp₀ : R < ‖p₀‖ := by
    rw [hp₀def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith [le_abs_self R]
  set W := connectedComponentIn Kᶜ p₀ with hWdef
  set Kh : Set ℂ := Wᶜ with hKhdef
  have hWo : IsOpen W := hK.isOpen_compl.connectedComponentIn
  have hWK : W ⊆ Kᶜ := connectedComponentIn_subset _ _
  have hKKh : K ⊆ Kh := fun v hv hvW => hWK hvW hv
  have hfar : ∀ v : ℂ, R < ‖v‖ → v ∈ W := fun v hv =>
    QuantumZipper.CA.Topo.subset_connectedComponentIn_compl_of_unbounded hR
      (QuantumZipper.CA.Topo.isPreconnected_setOf_lt_norm R) (GM.jb_not_isBounded_lt_norm R)
      (Set.disjoint_left.2 fun u hu huK =>
        QuantumZipper.CA.Topo.setOf_lt_norm_subset_compl hR hu huK) hp₀ hv
  have hKhc : IsCompact Kh := by
    refine Metric.isCompact_of_isClosed_isBounded hWo.isClosed_compl ?_
    refine (isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset fun v hv => ?_
    rw [mem_closedBall, dist_zero_right]
    by_contra h
    exact hv (hfar v (not_le.1 h))
  have hz : z₀ ∈ interior Kh := interior_mono hKKh hz₀
  have hfrKh : frontier Kh = frontier K := by
    rw [hKhdef, frontier_compl]; exact k8l_frontier_cc hK hJor hR hp₀
  have hz₀F : z₀ ∉ frontier K := fun h => h.2 hz₀
  have hJ : IsPreconnected (frontier Kh) := by
    rw [hfrKh]
    have := JordanMap.jm_isPreconnected_diff_of_isJordanCurve hJor z₀
    rwa [diff_singleton_eq_self hz₀F] at this
  have hJne : (frontier Kh).Nonempty := by
    rw [hfrKh]
    obtain ⟨γ, -, -, he⟩ := hJor
    rw [← he]
    exact (NormedSpace.sphere_nonempty.2 zero_le_one).image γ
  have hKp := DD.to_isPreconnected_K hKhc hJ hJne
  set Ω := DD.toOmega Kh z₀ with hΩ
  have hfr := DD.to_frontier_omega hKhc hz
  rw [hfrKh] at hfr
  have hcomp : ∀ a ∉ Ω, ¬ Bornology.IsBounded (connectedComponentIn Ωᶜ a) := by
    intro a ha hb
    have hzK : z₀ ∉ Kh \ {z₀} := fun h => h.2 rfl
    have hpc : IsPreconnected Ωᶜ := by
      rw [DD.to_compl_omega]
      exact (DD.to_isPreconnected_diff hKp hz).image _ (GM.jo_continuousOn_iota _ hzK)
    have hsub := hpc.subset_connectedComponentIn ha subset_rfl
    obtain ⟨r, hr, hΩs⟩ := DD.to_omega_subset hz
    refine GM.jb_not_isBounded_lt_norm (1 / r) (hb.subset (fun w hw => hsub fun hwΩ => ?_))
    have := hΩs hwΩ
    rw [mem_closedBall, dist_zero_right] at this
    exact not_le.2 hw this
  obtain ⟨r, hr, hΩs⟩ := DD.to_omega_subset hz
  have hKhcp : IsPreconnected Khᶜ := by
    rw [hKhdef, compl_compl]; exact isPreconnected_connectedComponentIn
  have hJΩ : JordanMap.IsJordanCurve (frontier Ω) := by
    rw [hfr]; exact k8l_jordan_inv hJor hz₀F
  obtain ⟨f, hfc, hfi, -, hf0, hfB, hfS⟩ := JordanMap.jm_jordan_closedDisc_extension'
    (DD.to_isOpen_omega hKhc hz) (DD.to_isPreconnected_omega hKhc hz hKhcp) (Or.inr rfl)
    ((isBounded_closedBall (x := (0 : ℂ))).subset hΩs) hcomp hJΩ
  rw [hfr] at hfS
  have hxz : x - z₀ ≠ 0 := sub_ne_zero.2 fun h => hz₀F (h ▸ hx)
  obtain ⟨ux, hux, hfux⟩ : (x - z₀)⁻¹ ∈ f '' sphere 0 1 := hfS ▸ mem_image_of_mem _ hx
  have hux1 : ‖ux‖ = 1 := mem_sphere_zero_iff_norm.1 hux
  have huxc : ux ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hux
  have hHc : ContinuousWithinAt (fun u => z₀ + (f u)⁻¹) (closedBall 0 1) ux :=
    continuousWithinAt_const.add ((hfc ux huxc).inv₀ (by rw [hfux]; exact inv_ne_zero hxz))
  have hHux : z₀ + (f ux)⁻¹ = x := by rw [hfux, inv_inv]; ring
  obtain ⟨η₀, hη₀, hη₀b⟩ := Metric.continuousWithinAt_iff.1 hHc ε hε
  set η := min η₀ (1 / 2) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨m, hm, hmb⟩ := k8l_inv_near hfc hfi huxc hη
  have hιc : ContinuousAt (fun v : ℂ => (v - z₀)⁻¹) x :=
    (continuousAt_id.sub continuousAt_const).inv₀ hxz
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.1 hιc m hm
  refine ⟨δ, hδ, fun y w hyw hy hwx x' hx' hx'x => ?_⟩
  -- `w` lies in `W`
  have hz₀K : z₀ ∈ K := interior_subset hz₀
  have hy0 : y ≠ 0 := fun h => by
    have := hy z₀ hz₀K; rw [h, norm_zero] at this; exact absurd this (not_lt.2 (norm_nonneg _))
  have hyW : y ∈ W := k8l_mem_cc_far hR hp₀ hy hy0
  have hwW : w ∈ W := by
    have hsub := (isPreconnected_range hyw.somePath.continuous).subset_connectedComponentIn
      ⟨0, hyw.somePath.source⟩ (by rintro _ ⟨t, rfl⟩; exact hyw.somePath_mem t)
    rw [← connectedComponentIn_eq hyW] at hsub
    exact hsub ⟨1, hyw.somePath.target⟩
  have hwz : w - z₀ ≠ 0 := sub_ne_zero.2 fun h => hWK hwW (h ▸ hz₀K)
  have hx'z : x' - z₀ ≠ 0 := sub_ne_zero.2 fun h => hz₀F (h ▸ hx')
  have hιw : (w - z₀)⁻¹ ∈ Ω := Or.inl (show z₀ + (w - z₀)⁻¹⁻¹ ∉ Kh by
    rw [inv_inv, add_sub_cancel]; exact fun h => h hwW)
  rw [hΩ, ← hfB] at hιw
  obtain ⟨u₁, hu₁, hfu₁⟩ := hιw
  obtain ⟨u₂, hu₂, hfu₂⟩ : (x' - z₀)⁻¹ ∈ f '' sphere 0 1 := hfS ▸ mem_image_of_mem _ hx'
  have hu₁c : u₁ ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hu₁
  have hu₂c : u₂ ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hu₂
  have hd₁ : dist u₁ ux < η := hmb u₁ hu₁c (by
    rw [hfu₁, hfux, ← dist_eq_norm]; exact hδb hwx)
  have hd₂ : dist u₂ ux < η := hmb u₂ hu₂c (by
    rw [hfu₂, hfux, ← dist_eq_norm]; exact hδb hx'x)
  -- the segment `[u₁, u₂]`
  set seg : unitInterval → ℂ := fun t => u₁ + (t : ℝ) • (u₂ - u₁) with hseg
  have hsegc : Continuous seg := by fun_prop
  have hsegB : ∀ t, seg t ∈ ball ux η := fun t =>
    (convex_ball ux η).add_smul_sub_mem hd₁ hd₂ ⟨t.2.1, t.2.2⟩
  have hsegC : ∀ t, seg t ∈ closedBall (0 : ℂ) 1 := fun t =>
    (convex_closedBall (0 : ℂ) 1).add_smul_sub_mem hu₁c hu₂c ⟨t.2.1, t.2.2⟩
  have hsegO : ∀ t : unitInterval, (t : ℝ) < 1 → seg t ∈ ball (0 : ℂ) 1 := by
    intro t ht
    have he : seg t = (1 - (t : ℝ)) • u₁ + (t : ℝ) • u₂ := by
      simp only [hseg, smul_sub, sub_smul, one_smul]; abel
    rw [mem_ball_zero_iff, he]
    have h1 : ‖u₁‖ < 1 := mem_ball_zero_iff.1 hu₁
    have h2 : ‖u₂‖ = 1 := mem_sphere_zero_iff_norm.1 hu₂
    calc ‖(1 - (t : ℝ)) • u₁ + (t : ℝ) • u₂‖ ≤ ‖(1 - (t : ℝ)) • u₁‖ + ‖(t : ℝ) • u₂‖ :=
          norm_add_le _ _
      _ = (1 - (t : ℝ)) * ‖u₁‖ + (t : ℝ) * ‖u₂‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith), abs_of_nonneg t.2.1]
      _ < 1 := by rw [h2]; nlinarith [t.2.1]
  have hseg0 : ∀ t, seg t ≠ 0 := fun t h => by
    have := hsegB t
    rw [h, mem_ball, dist_comm, dist_zero_right, hux1] at this
    have : η ≤ 1 / 2 := min_le_right _ _
    linarith
  have hfseg0 : ∀ t, f (seg t) ≠ 0 := fun t h =>
    hseg0 t (hfi (hsegC t) (mem_closedBall_self zero_le_one) (h.trans hf0.symm))
  have hβc : Continuous fun t => z₀ + (f (seg t))⁻¹ :=
    continuous_const.add ((hfc.comp_continuous hsegc hsegC).inv₀ hfseg0)
  have hs0 : seg 0 = u₁ := by simp [hseg]
  have hs1 : seg 1 = u₂ := by simp [hseg]
  let β : Path w x' :=
    { toFun := fun t => z₀ + (f (seg t))⁻¹
      continuous_toFun := hβc
      source' := by
        show z₀ + (f (seg 0))⁻¹ = w
        rw [hs0, hfu₁, inv_inv]; ring
      target' := by
        show z₀ + (f (seg 1))⁻¹ = x'
        rw [hs1, hfu₂, inv_inv]; ring }
  refine ⟨β, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    have := hη₀b (hsegC t) (lt_of_lt_of_le (hsegB t) (min_le_left _ _))
    rw [hHux] at this
    exact this
  · rintro _ ⟨⟨t, rfl⟩, htK⟩
    by_cases ht : (t : ℝ) < 1
    · exfalso
      have hmem : f (seg t) ∈ Ω := by rw [hΩ, ← hfB]; exact mem_image_of_mem f (hsegO t ht)
      rcases hmem with h | h
      · exact h (hKKh htK)
      · exact hfseg0 t h
    · have ht1 : t = 1 := Subtype.ext (le_antisymm t.2.2 (not_lt.1 ht))
      rw [ht1]
      exact β.target

end LQGMetric.CONF
