/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412cInt at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanJ1bFinal
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupStop
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoEilenberg

/-!
# The interior of a filled metric ball is connected (input `hint` of `theta_bounded`)

DEC-86 item (4) (decisions/DEC-86.md). GM L4.13′ (`lem-geo-disconnect`,
`literature/src/1905.00383/uniqueness-final.tex` l. 2071–2093) uses that `𝓑^•_s` is a closed
Jordan domain; the crosscut tool `Topo.Crosscut.theta_bounded` needs
`IsPreconnected (interior 𝓑^•_s)`.

Route (no Jordan curve theorem): for `a, b ∈ int K`, the function
`F(w) = (Ψ w − a)/(Ψ w − b)` (`F 0 = 1`) is continuous and zero-free on `cl 𝔻`, where `Ψ` is the
exterior conformal map `gm_filledBall_conformal'`; lifting the homotopy `(t, u) ↦ F(t u)` through
`exp` (`IsCoveringMap.liftHomotopy`) gives a continuous logarithm of `F` on `∂𝔻`, hence of
`(x − a)/(x − b)` on `Γ = Ψ(∂𝔻) = ∂K`. Eilenberg's criterion (QuantumZipper
`CA.Topo.not_separates_of_hasLogOn`, Burckel, *Classical Analysis in the Complex Plane*,
Ex. 4.37(i)) shows that `Γ` does not separate `a` from `b`. Own elementary argument
(DV-D86d).

* `p412c_invFun_contOn_sphere` — inverse of a map injective and continuous on `∂𝔻`.
* `p412c_hasLog_sphere` — a zero-free continuous function on `cl 𝔻` has a log on `∂𝔻`.
* `p412c_interior_isPreconnected_of_ext` — the general statement for a closed `K` with such `Ψ`.
* `p412c_filledBall_interior_isPreconnected` — `IsPreconnected (interior 𝓑^•_s)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace LQGMetric.GM

/-- The inverse of a map continuous and injective on `∂𝔻` is continuous on the image
(compact-to-Hausdorff; as `CONF.l214_invFun_contOn`). -/
theorem p412c_invFun_contOn_sphere {Φ : ℂ → ℂ} (hc : ContinuousOn Φ (sphere 0 1))
    (hinj : InjOn Φ (sphere 0 1)) :
    ContinuousOn (Function.invFunOn Φ (sphere 0 1)) (Φ '' sphere 0 1) := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  refine ⟨Φ '' (sphere 0 1 ∩ t),
    (((isCompact_sphere 0 1).inter_right ht).image_of_continuousOn
      (hc.mono inter_subset_left)).isClosed, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, ζ, hζ, rfl⟩
    rw [mem_preimage, hinj.leftInvOn_invFunOn hζ] at hy
    exact ⟨⟨ζ, ⟨hζ, hy⟩, rfl⟩, ζ, hζ, rfl⟩
  · rintro ⟨⟨ζ, ⟨hζ, hζt⟩, rfl⟩, -⟩
    refine ⟨?_, ζ, hζ, rfl⟩
    rw [mem_preimage, hinj.leftInvOn_invFunOn hζ]; exact hζt

/-- A continuous zero-free function on `cl 𝔻` has a continuous logarithm on `∂𝔻` (lift of the
homotopy `(t, u) ↦ F(t u)` through `exp`). -/
theorem p412c_hasLog_sphere {F : ℂ → ℂ} (hF : ContinuousOn F (closedBall 0 1))
    (hF0 : ∀ w ∈ closedBall (0 : ℂ) 1, F w ≠ 0) :
    ∃ L : ℂ → ℂ, ContinuousOn L (sphere 0 1) ∧ ∀ w ∈ sphere (0 : ℂ) 1, Complex.exp (L w) = F w := by
  classical
  have hmem : ∀ (t : unitInterval) (u : sphere (0 : ℂ) 1),
      ((t : ℝ) : ℂ) * (u : ℂ) ∈ closedBall (0 : ℂ) 1 := by
    intro t u
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg t.2.1, norm_eq_of_mem_sphere u]
    simpa using t.2.2
  let H : C(unitInterval × sphere (0 : ℂ) 1, {z : ℂ // z ≠ 0}) :=
    ⟨fun p => ⟨F (((p.1 : ℝ) : ℂ) * (p.2 : ℂ)), hF0 _ (hmem p.1 p.2)⟩, by
      refine Continuous.subtype_mk ?_ _
      refine hF.comp_continuous (by fun_prop) fun p => hmem p.1 p.2⟩
  let f : C(sphere (0 : ℂ) 1, ℂ) := ContinuousMap.const _ (Complex.log (F 0))
  have H0 : ∀ a, H (0, a) = (fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) (f a) := by
    intro a
    apply Subtype.ext
    simp only [H, f, ContinuousMap.coe_mk, ContinuousMap.const_apply, Set.Icc.coe_zero,
      Complex.ofReal_zero, zero_mul]
    exact (Complex.exp_log (hF0 0 (mem_closedBall_self zero_le_one))).symm
  let G := Complex.isCoveringMap_exp.liftHomotopy H f H0
  have hG := Complex.isCoveringMap_exp.liftHomotopy_lifts H f H0
  refine ⟨fun w => if hw : w ∈ sphere (0 : ℂ) 1 then G (1, ⟨w, hw⟩) else 0, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (sphere (0 : ℂ) 1).domRestrict
        (fun w => if hw : w ∈ sphere (0 : ℂ) 1 then G (1, ⟨w, hw⟩) else 0) =
        fun u => G (1, u) := by
      funext u; simp
    rw [this]
    fun_prop
  · intro w hw
    simp only [hw, dite_true]
    have := congrArg Subtype.val (congr_fun hG (1, ⟨w, hw⟩))
    simp only [Function.comp_apply] at this
    rw [this]
    simp [H]

/-- `(z − a)/(z − b) → 1` at infinity. -/
theorem p412c_tendsto_ratio (a b : ℂ) :
    Tendsto (fun z : ℂ => (z - a) / (z - b)) (Bornology.cobounded ℂ) (𝓝 1) := by
  have hinv : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := tendsto_inv₀_cobounded
  have h1 : Tendsto (fun z : ℂ => (1 - a * z⁻¹) / (1 - b * z⁻¹)) (Bornology.cobounded ℂ)
      (𝓝 ((1 - a * 0) / (1 - b * 0))) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)).div
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)) (by simp)
  simp only [mul_zero, sub_zero, div_one] at h1
  refine h1.congr' ?_
  filter_upwards [Bornology.eventually_ne_cobounded (0 : ℂ)] with z hz
  rw [show (1 : ℂ) - a * z⁻¹ = (z - a) / z by field_simp,
    show (1 : ℂ) - b * z⁻¹ = (z - b) / z by field_simp, div_div_div_cancel_right₀ hz]

theorem p412c_sphere_subset : sphere (0 : ℂ) 1 ⊆ closedBall 0 1 \ {0} := fun w hw =>
  ⟨sphere_subset_closedBall hw, fun h => by
    rw [mem_singleton_iff.1 h, mem_sphere, dist_self] at hw; exact zero_ne_one hw⟩

/-- **`int K` is preconnected** for a closed `K` whose complement is the image of the punctured
disc under a map `Ψ` continuous on `cl 𝔻 ∖ {0}`, injective on `∂𝔻`, with `Ψ(∂𝔻) = ∂K` and
`Ψ → ∞` at `0`. -/
theorem p412c_interior_isPreconnected_of_ext {K : Set ℂ} (hK : IsClosed K) {Ψ : ℂ → ℂ}
    (hc : ContinuousOn Ψ (closedBall 0 1 \ {0})) (hi : InjOn Ψ (sphere 0 1))
    (hB : Ψ '' (ball 0 1 \ {0}) = Kᶜ) (hS : Ψ '' sphere 0 1 = frontier K)
    (hT : Tendsto Ψ (𝓝[≠] 0) (Bornology.cobounded ℂ)) : IsPreconnected (interior K) := by
  have hΓc : IsCompact (frontier K) :=
    hS ▸ (isCompact_sphere 0 1).image_of_continuousOn (hc.mono p412c_sphere_subset)
  have hnf : ∀ c ∈ interior K, c ∉ frontier K := fun c hc' h => h.2 hc'
  -- `Ψ` misses `int K` on `cl 𝔻 ∖ {0}`
  have hmiss : ∀ c ∈ interior K, ∀ w ∈ closedBall (0 : ℂ) 1 \ {0}, Ψ w ≠ c := by
    intro c hc' w hw he
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.1 hw.1) with h | h
    · have : Ψ w ∈ Kᶜ := hB ▸ mem_image_of_mem Ψ ⟨mem_ball_zero_iff.2 h, hw.2⟩
      exact this (he ▸ interior_subset hc')
    · have : Ψ w ∈ frontier K := hS ▸ mem_image_of_mem Ψ (mem_sphere_zero_iff_norm.2 h)
      exact hnf c hc' (he ▸ this)
  have hsep : ∀ a ∈ interior K, ∀ b ∈ interior K,
      b ∈ connectedComponentIn (frontier K)ᶜ a := by
    intro a ha b hb
    set F : ℂ → ℂ := fun w => if w = 0 then 1 else (Ψ w - a) / (Ψ w - b) with hFdef
    have hon : ContinuousOn (fun w => (Ψ w - a) / (Ψ w - b)) (closedBall 0 1 \ {0}) :=
      (hc.sub continuousOn_const).div (hc.sub continuousOn_const)
        fun w hw => sub_ne_zero.2 (hmiss b hb w hw)
    have hFc : ContinuousOn F (closedBall 0 1) := by
      intro w hw
      by_cases hw0 : w = 0
      · subst hw0
        rw [← continuousWithinAt_sdiff_self]
        have hlim : Tendsto (fun w => (Ψ w - a) / (Ψ w - b)) (𝓝[≠] (0 : ℂ)) (𝓝 1) :=
          (p412c_tendsto_ratio a b).comp hT
        have hF0 : F 0 = 1 := by simp [F]
        rw [ContinuousWithinAt, hF0]
        refine (hlim.mono_left (nhdsWithin_mono _ fun x hx => hx.2)).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        simp [F, show x ≠ 0 from hx.2]
      · have hmem : closedBall (0 : ℂ) 1 ∩ {0}ᶜ ∈ 𝓝[closedBall 0 1] w :=
          inter_mem_nhdsWithin _ (isOpen_compl_singleton.mem_nhds hw0)
        have h1 : ContinuousWithinAt (fun w => (Ψ w - a) / (Ψ w - b)) (closedBall 0 1) w :=
          (hon w ⟨hw, hw0⟩).mono_of_mem_nhdsWithin hmem
        refine h1.congr_of_eventuallyEq ?_ ?_
        · filter_upwards [hmem] with x hx
          simp [F, show x ≠ 0 from hx.2]
        · simp [F, hw0]
    have hF0 : ∀ w ∈ closedBall (0 : ℂ) 1, F w ≠ 0 := by
      intro w hw
      by_cases hw0 : w = 0
      · simp [F, hw0]
      · simp only [F, hw0, ite_false]
        exact div_ne_zero (sub_ne_zero.2 (hmiss a ha w ⟨hw, hw0⟩))
          (sub_ne_zero.2 (hmiss b hb w ⟨hw, hw0⟩))
    obtain ⟨L, hLc, hL⟩ := p412c_hasLog_sphere hFc hF0
    have hex : ∀ x ∈ frontier K, ∃ w ∈ sphere (0 : ℂ) 1, Ψ w = x := fun x hx => by
      rw [← hS] at hx; exact hx
    have hlog : QuantumZipper.CA.Topo.HasLogOn (fun x => (x - a) / (x - b)) (frontier K) := by
      refine ⟨fun x => L (Function.invFunOn Ψ (sphere 0 1) x), ?_, fun x hx => ?_⟩
      · refine hLc.comp ?_ fun x hx => Function.invFunOn_mem (hex x hx)
        have := p412c_invFun_contOn_sphere (hc.mono p412c_sphere_subset) hi
        rwa [hS] at this
      · have hw := Function.invFunOn_mem (hex x hx)
        have hΨ := Function.invFunOn_eq (hex x hx)
        rw [hL _ hw]
        have hne : Function.invFunOn Ψ (sphere 0 1) x ≠ 0 := (p412c_sphere_subset hw).2
        simp only [F, hne, ite_false, hΨ]
    exact QuantumZipper.CA.Topo.not_separates_of_hasLogOn hΓc (hnf a ha) (hnf b hb) hlog
  refine isPreconnected_of_forall_pair fun a ha b hb =>
    ⟨connectedComponentIn (frontier K)ᶜ a, ?_, mem_connectedComponentIn (hnf a ha),
      hsep a ha b hb, isPreconnected_connectedComponentIn⟩
  have hcov : (frontier K)ᶜ ⊆ interior K ∪ Kᶜ := by
    intro x hx
    by_cases hxK : x ∈ K
    · left
      by_contra hni
      exact hx ⟨subset_closure hxK, hni⟩
    · exact Or.inr hxK
  exact isPreconnected_connectedComponentIn.subset_left_of_subset_union isOpen_interior
    hK.isOpen_compl (disjoint_compl_right.mono_left interior_subset)
    ((connectedComponentIn_subset _ _).trans hcov)
    ⟨a, mem_connectedComponentIn (hnf a ha), ha⟩

/-- **`IsPreconnected (interior 𝓑^•_s)`** (DEC-86 (4); input `hint` of `theta_bounded` for
GM L4.13′). -/
theorem p412c_filledBall_interior_isPreconnected {D : ContMetric} {z : ℂ} {s : ℝ} (hs : 0 < s)
    (hL : D.IsLength) (hbd : Bornology.IsBounded (Blueprint.ballM D z s)) :
    IsPreconnected (interior (Blueprint.filledBall D z s)) := by
  obtain ⟨Ψ, hc, hi, -, hB, hS, hT⟩ := gm_filledBall_conformal' hs hL hbd
  exact p412c_interior_isPreconnected_of_ext (gm_filledBall_isClosed D z s) hc
    (hi.mono p412c_sphere_subset) hB hS hT

end LQGMetric.GM
