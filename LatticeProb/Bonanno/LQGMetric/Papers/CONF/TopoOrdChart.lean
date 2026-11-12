/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.TopoOrdChart at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.TopoOrdCara2
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeBasic

/-!
# TOPO-ORD, step 2b: log charts of the closed exterior of `K`

From the Carathéodory map `f` of `Ω(K)` (`to_disc_map`), write `f(w) = w g(w)` with `g`
continuous and zero-free on `𝔻̄` (`g(0) = f′(0) ≠ 0`, QuantumZipper
`Koebe.deriv_ne_zero_of_injOn`), and let `Λ(σ, t)` be the continuous logarithm of
`g(σ e^{-it})` (homotopy lifting through `exp`, as in `posLift_of_disc_map`, `LiftPos.lean`).
The **chart** `L(ζ) = ζ − Λ(e^{-Re ζ}, Im ζ)` on the closed half plane `Re ζ ≥ 0` satisfies
`z + e^{L(ζ)} = z + 1/f(e^{-ζ})`: it maps `{Re ζ ≥ 0}` bijectively onto the log-lift of
`ℂ ∖ int K`, the line `Re ζ = 0` onto the lift of `∂K`, commutes with `ζ ↦ ζ + 2πi`, and
`L(ζ) − ζ` is bounded and tends to a constant as `Re ζ → ∞` (`IsChart`).
Own elementary argument (standard), DV-CONF-TO1.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter

namespace LQGMetric.CONF.DD

/-- a log chart of `ℂ ∖ int K` around `z` -/
structure IsChart (K : Set ℂ) (z : ℂ) (L : ℂ → ℂ) : Prop where
  cont : Continuous L
  per : ∀ ζ, L (ζ + 2 * Real.pi * Complex.I) = L ζ + 2 * Real.pi * Complex.I
  inj : InjOn L {ζ | 0 ≤ ζ.re}
  bdd : ∃ C, ∀ ζ : ℂ, 0 ≤ ζ.re → ‖L ζ - ζ‖ ≤ C
  asym : ∃ c : ℂ, ∀ ε > 0, ∃ R, ∀ ζ : ℂ, R ≤ ζ.re → ‖L ζ - ζ - c‖ < ε
  surj : ∀ w : ℂ, z + Complex.exp w ∉ interior K → ∃ ζ, 0 ≤ ζ.re ∧ L ζ = w
  out : ∀ ζ : ℂ, 0 < ζ.re → z + Complex.exp (L ζ) ∉ K
  bdy : ∀ ζ : ℂ, ζ.re = 0 → z + Complex.exp (L ζ) ∈ frontier K

theorem two_pi_I_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

theorem exp_neg_mem_closedBall {ζ : ℂ} (h : 0 ≤ ζ.re) :
    Complex.exp (-ζ) ∈ closedBall (0 : ℂ) 1 := by
  rw [mem_closedBall_zero_iff, Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff]; linarith

theorem exp_neg_mem_ball {ζ : ℂ} (h : 0 < ζ.re) : Complex.exp (-ζ) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, Complex.norm_exp, Complex.neg_re, Real.exp_lt_one_iff]; linarith

theorem exp_neg_mem_sphere {ζ : ℂ} (h : ζ.re = 0) : Complex.exp (-ζ) ∈ sphere (0 : ℂ) 1 := by
  rw [mem_sphere_zero_iff_norm, Complex.norm_exp, Complex.neg_re, h, neg_zero, Real.exp_zero]

theorem exists_reduce (t : ℝ) : ∃ t' ∈ Icc (0 : ℝ) (2 * Real.pi), ∃ n : ℤ,
    t = t' + n * (2 * Real.pi) := by
  have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 := Int.floor_le (t / (2 * Real.pi))
  have h3 := Int.lt_floor_add_one (t / (2 * Real.pi))
  rw [le_div_iff₀ h2] at h1
  rw [div_lt_iff₀ h2] at h3
  exact ⟨t - ⌊t / (2 * Real.pi)⌋ * (2 * Real.pi), ⟨by linarith, by nlinarith⟩,
    ⌊t / (2 * Real.pi)⌋, by ring⟩

/-- integer periodicity from periodicity -/
theorem periodic_int {β : Type*} {F : ℝ → β} (h : ∀ t, F (t + 2 * Real.pi) = F t) (t : ℝ)
    (n : ℤ) : F (t + n * (2 * Real.pi)) = F t := by
  induction n using Int.induction_on generalizing t with
  | zero => simp
  | succ k ih => rw [← ih t]; push_cast; rw [add_one_mul, ← add_assoc, h]
  | pred k ih =>
    rw [← ih t]; push_cast
    have := h (t + (-(k : ℝ) - 1) * (2 * Real.pi))
    rw [← this]; congr 1; ring

/-- the chart of the closed exterior from a Carathéodory map `f` of `Ω(K)` -/
theorem isChart_of_disc_map {K : Set ℂ} {z : ℂ} {f : ℂ → ℂ}
    (hfc : ContinuousOn f (closedBall 0 1)) (hfi : InjOn f (closedBall 0 1))
    (hfd : DifferentiableOn ℂ f (ball 0 1)) (hf0 : f 0 = 0) (hfB : f '' ball 0 1 = toOmega K z)
    (hfs : f '' sphere 0 1 = (fun x => (x - z)⁻¹) '' frontier K) (hK : IsClosed K) :
    ∃ L, IsChart K z L := by
  classical
  set g : ℂ → ℂ := fun w => if w = 0 then deriv f 0 else f w / w with hg
  have h0b : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hd0 : deriv f 0 ≠ 0 :=
    QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn isOpen_ball hfd
      (hfi.mono ball_subset_closedBall) h0b
  have hfne : ∀ w ∈ closedBall (0 : ℂ) 1, w ≠ 0 → f w ≠ 0 := fun w hw hw0 h =>
    hw0 (hfi hw (mem_closedBall_self zero_le_one) (h.trans hf0.symm))
  have hgne : ∀ w ∈ closedBall (0 : ℂ) 1, g w ≠ 0 := by
    intro w hw
    by_cases hw0 : w = 0
    · simp only [hg, hw0, if_true]; exact hd0
    · simp only [hg, hw0, if_false]; exact div_ne_zero (hfne w hw hw0) hw0
  have hgc : ContinuousOn g (closedBall 0 1) := by
    intro w hw
    by_cases hw0 : w = 0
    · subst hw0
      have hda : HasDerivAt f (deriv f 0) 0 :=
        ((hfd 0 h0b).differentiableAt (isOpen_ball.mem_nhds h0b)).hasDerivAt
      have ht := hda.tendsto_slope_zero
      simp only [zero_add, hf0, sub_zero] at ht
      have hca : ContinuousAt g 0 := by
        rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
        have he : g =ᶠ[𝓝[≠] (0 : ℂ)] fun t => t⁻¹ • f t := by
          filter_upwards [self_mem_nhdsWithin] with t ht0
          have ht0' : t ≠ 0 := ht0
          simp only [hg, if_neg ht0', smul_eq_mul, div_eq_mul_inv]; ring
        simp only [hg, if_true]
        exact ht.congr' he.symm
      exact hca.continuousWithinAt
    · have hcw : ContinuousWithinAt (fun w => f w / w) (closedBall 0 1) w :=
        (hfc w hw).div continuousWithinAt_id hw0
      refine hcw.congr_of_eventuallyEq ?_ (by simp only [hg, if_neg hw0])
      filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hw0)] with t ht0
      simp only [hg, if_neg (show t ≠ 0 from ht0)]
  have hmem : ∀ (σ : unitInterval) (t : ℝ),
      (σ : ℂ) * Complex.exp (-(t : ℂ) * Complex.I) ∈ closedBall (0 : ℂ) 1 := by
    intro σ t
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_exp]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg σ.2.1]
    have : (-(t : ℂ) * Complex.I).re = 0 := by simp
    rw [this, Real.exp_zero, mul_one]; exact σ.2.2
  have hHc : Continuous fun p : unitInterval × ℝ =>
      g ((p.1 : ℂ) * Complex.exp (-(p.2 : ℂ) * Complex.I)) :=
    hgc.comp_continuous (by fun_prop) (fun p => hmem p.1 p.2)
  let H : C(unitInterval × ℝ, {w : ℂ // w ≠ 0}) :=
    ⟨fun p => ⟨g ((p.1 : ℂ) * Complex.exp (-(p.2 : ℂ) * Complex.I)), hgne _ (hmem p.1 p.2)⟩,
      hHc.subtype_mk _⟩
  have hg0 : g 0 ≠ 0 := hgne 0 (mem_closedBall_self zero_le_one)
  let c0 : C(ℝ, ℂ) := ContinuousMap.const ℝ (Complex.log (g 0))
  have H0 : ∀ t, H (0, t) = (fun w : ℂ => (⟨Complex.exp w, Complex.exp_ne_zero w⟩ :
      {w : ℂ // w ≠ 0})) (c0 t) := by
    intro t
    apply Subtype.ext
    simp [H, c0, Complex.exp_log hg0]
  set Λ := Complex.isCoveringMap_exp.liftHomotopy H c0 H0 with hΛ
  have hΛe : ∀ p, Complex.exp (Λ p) = g ((p.1 : ℂ) * Complex.exp (-(p.2 : ℂ) * Complex.I)) := by
    intro p
    have := congrArg Subtype.val
      (congr_fun (Complex.isCoveringMap_exp.liftHomotopy_lifts H c0 H0) p)
    exact this
  have hΛ0 : ∀ t, Λ (0, t) = Complex.log (g 0) := fun t =>
    Complex.isCoveringMap_exp.liftHomotopy_zero H c0 H0 t
  -- periodicity of `Λ(σ, ·)` for every `σ`
  have hper : ∀ (σ₀ : unitInterval) t, Λ (σ₀, t + 2 * Real.pi) = Λ (σ₀, t) := by
    intro σ₀ t
    have hexp : Complex.exp (-((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
        Complex.exp (-(t : ℂ) * Complex.I) := by
      rw [show -((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
        -(t : ℂ) * Complex.I + ((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hmaps : MapsTo (fun σ : unitInterval => (Λ (σ, t + 2 * Real.pi) - Λ (σ, t)) /
        (2 * Real.pi * Complex.I)) univ (range ((↑) : ℤ → ℂ)) := by
      intro σ _
      have he : Complex.exp (Λ (σ, t + 2 * Real.pi) - Λ (σ, t)) = 1 := by
        rw [Complex.exp_sub, hΛe, hΛe]
        simp only
        rw [hexp, div_self (hgne _ (hmem σ t))]
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 he
      exact ⟨n, by simp only [hn, mul_div_cancel_right₀ _ two_pi_I_ne]⟩
    have hcont : Continuous fun σ : unitInterval =>
        (Λ (σ, t + 2 * Real.pi) - Λ (σ, t)) / (2 * Real.pi * Complex.I) := by
      have := Λ.continuous; fun_prop
    have hcon := isPreconnected_univ.constant_of_mapsTo
      Complex.isClosedEmbedding_intCast.isInducing.isDiscrete_range hcont.continuousOn hmaps
      (mem_univ σ₀) (mem_univ (0 : unitInterval))
    simp only [hΛ0, sub_self, zero_div, div_eq_zero_iff, two_pi_I_ne, or_false,
      sub_eq_zero] at hcon
    exact hcon
  have hred : ∀ (σ : unitInterval) (t : ℝ), ∃ t' ∈ Icc (0 : ℝ) (2 * Real.pi),
      Λ (σ, t) = Λ (σ, t') := by
    intro σ t
    obtain ⟨t', ht', n, rfl⟩ := exists_reduce t
    exact ⟨t', ht', periodic_int (F := fun s => Λ (σ, s)) (hper σ) t' n⟩
  -- the chart
  let σf : ℂ → unitInterval := fun ζ => Set.projIcc 0 1 zero_le_one (Real.exp (-ζ.re))
  have hσc : Continuous σf := continuous_projIcc.comp (by fun_prop)
  have hσv : ∀ ζ : ℂ, 0 ≤ ζ.re → ((σf ζ : unitInterval) : ℝ) = Real.exp (-ζ.re) := by
    intro ζ hζ
    simp only [σf]
    rw [Set.projIcc_of_mem]
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by linarith)⟩
  set L : ℂ → ℂ := fun ζ => ζ - Λ (σf ζ, ζ.im) with hL
  have hLc : Continuous L := continuous_id.sub (Λ.continuous.comp (hσc.prodMk (by fun_prop)))
  have hpt : ∀ ζ : ℂ, 0 ≤ ζ.re →
      ((σf ζ : ℝ) : ℂ) * Complex.exp (-(ζ.im : ℂ) * Complex.I) = Complex.exp (-ζ) := by
    intro ζ hζ
    rw [hσv ζ hζ, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp
  have hLe : ∀ ζ : ℂ, 0 ≤ ζ.re → Complex.exp (L ζ) = (f (Complex.exp (-ζ)))⁻¹ := by
    intro ζ hζ
    simp only [hL]
    rw [Complex.exp_sub, hΛe]
    simp only
    rw [hpt ζ hζ]
    simp only [hg, if_neg (Complex.exp_ne_zero _)]
    rw [div_div_eq_mul_div, Complex.exp_neg, div_eq_mul_inv, mul_inv_cancel₀ (Complex.exp_ne_zero _), one_mul]
  have hLper : ∀ ζ, L (ζ + 2 * Real.pi * Complex.I) = L ζ + 2 * Real.pi * Complex.I := by
    intro ζ
    have h1 : σf (ζ + 2 * Real.pi * Complex.I) = σf ζ := by simp [σf]
    have h2 : (ζ + 2 * Real.pi * Complex.I).im = ζ.im + 2 * Real.pi := by simp
    simp only [hL, h1, h2, hper]; ring
  have hLper' : ∀ ζ (n : ℤ), L (ζ + n * (2 * Real.pi * Complex.I)) =
      L ζ + n * (2 * Real.pi * Complex.I) := by
    intro ζ n
    have := periodic_int (F := fun t : ℝ => L (ζ + (t : ℂ) * Complex.I) - (t : ℂ) * Complex.I)
      (fun t => by
        rw [show ζ + ((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
          ζ + (t : ℂ) * Complex.I + 2 * Real.pi * Complex.I by push_cast; ring, hLper]
        push_cast; ring) 0 n
    simp only [zero_add, Complex.ofReal_zero, zero_mul, add_zero, sub_zero] at this
    rw [show ζ + n * (2 * Real.pi * Complex.I) = ζ + ((n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I
      by push_cast; ring]
    rw [sub_eq_iff_eq_add] at this
    rw [this]; push_cast; ring
  refine ⟨L, ⟨hLc, hLper, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- injectivity
    intro ζ hζ ζ' hζ' h
    have hζ0 : (0:ℝ) ≤ ζ.re := hζ
    have hζ0' : (0:ℝ) ≤ ζ'.re := hζ'
    have h1 : f (Complex.exp (-ζ)) = f (Complex.exp (-ζ')) := by
      have := congrArg Complex.exp h
      rw [hLe ζ hζ0, hLe ζ' hζ0'] at this
      exact inv_injective this
    have h2 := hfi (exp_neg_mem_closedBall hζ0) (exp_neg_mem_closedBall hζ0') h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h2
    have hz' : ζ' = ζ + ((n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      linear_combination hn
    rw [hz', hLper'] at h
    have : ((n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) = 0 := by linear_combination -h
    rw [hz', this, add_zero]
  · -- boundedness
    obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_Icc (a := (0:ℝ)) (b := 2 * Real.pi))).exists_bound_of_continuousOn Λ.continuous.continuousOn
    refine ⟨C, fun ζ _ => ?_⟩
    obtain ⟨t', ht', he⟩ := hred (σf ζ) ζ.im
    simp only [hL, sub_sub_cancel_left, norm_neg, he]
    exact hC _ ⟨mem_univ _, ht'⟩
  · -- asymptotics
    refine ⟨-Complex.log (g 0), fun ε hε => ?_⟩
    have huc := (isCompact_univ.prod (isCompact_Icc (a := (0:ℝ)) (b := 2 * Real.pi))).uniformContinuousOn_of_continuous Λ.continuous.continuousOn
    obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
    refine ⟨max 0 (Real.log (2 / δ)), fun ζ hζ => ?_⟩
    have hζ0 : 0 ≤ ζ.re := (le_max_left _ _).trans hζ
    have hζ1 : Real.log (2 / δ) ≤ ζ.re := (le_max_right _ _).trans hζ
    have hσδ : ((σf ζ : unitInterval) : ℝ) < δ := by
      rw [hσv ζ hζ0]
      have : Real.exp (-ζ.re) ≤ Real.exp (-Real.log (2 / δ)) := Real.exp_le_exp.2 (by linarith)
      have e : Real.exp (-Real.log (2 / δ)) = δ / 2 := by
        rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
      linarith
    obtain ⟨t', ht', he⟩ := hred (σf ζ) ζ.im
    have hd : dist (σf ζ, t') ((0 : unitInterval), t') < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Subtype.dist_eq]
      simp only [Set.Icc.coe_zero, dist_zero_right, Real.norm_eq_abs]
      rw [abs_of_nonneg (σf ζ).2.1]; exact hσδ
    have := hU _ ⟨mem_univ _, ht'⟩ _ ⟨mem_univ _, ht'⟩ hd
    rw [dist_eq_norm, hΛ0] at this
    simp only [hL, he]
    rw [show ζ - Λ (σf ζ, t') - ζ - -Complex.log (g 0) = -(Λ (σf ζ, t') - Complex.log (g 0))
      by ring, norm_neg]
    exact this
  · -- surjectivity
    intro w hw
    have hq : ∃ q ∈ closedBall (0 : ℂ) 1, f q = Complex.exp (-w) := by
      by_cases hxK : z + Complex.exp w ∈ K
      · have hxF : z + Complex.exp w ∈ frontier K := by
          rw [frontier, hK.closure_eq]; exact ⟨hxK, hw⟩
        have : Complex.exp (-w) ∈ f '' sphere 0 1 := by
          rw [hfs]; exact ⟨_, hxF, by show (z + Complex.exp w - z)⁻¹ = _; rw [add_sub_cancel_left, Complex.exp_neg]⟩
        obtain ⟨q, hq, hfq⟩ := this
        exact ⟨q, sphere_subset_closedBall hq, hfq⟩
      · have : Complex.exp (-w) ∈ f '' ball 0 1 := by
          rw [hfB]; left; show z + (Complex.exp (-w))⁻¹ ∉ K
          rwa [Complex.exp_neg, inv_inv]
        obtain ⟨q, hq, hfq⟩ := this
        exact ⟨q, ball_subset_closedBall hq, hfq⟩
    obtain ⟨q, hq, hfq⟩ := hq
    have hq0 : q ≠ 0 := by
      rintro rfl; rw [hf0] at hfq; exact Complex.exp_ne_zero _ hfq.symm
    set ζ₀ := -Complex.log q
    have hζ₀ : 0 ≤ ζ₀.re := by
      simp only [ζ₀, Complex.neg_re, Complex.log_re, Left.nonneg_neg_iff]
      exact Real.log_nonpos (norm_nonneg _) (mem_closedBall_zero_iff.1 hq)
    have he : Complex.exp (L ζ₀) = Complex.exp w := by
      rw [hLe ζ₀ hζ₀]
      simp only [ζ₀, neg_neg, Complex.exp_log hq0, hfq, Complex.exp_neg, inv_inv]
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
    refine ⟨ζ₀ + ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I), by simpa using hζ₀, ?_⟩
    rw [hLper', hn]; push_cast; ring
  · -- open part
    intro ζ hζ
    have hq := exp_neg_mem_ball hζ
    have hmem : f (Complex.exp (-ζ)) ∈ toOmega K z := hfB ▸ mem_image_of_mem f hq
    have hne : f (Complex.exp (-ζ)) ≠ 0 :=
      hfne _ (ball_subset_closedBall hq) (Complex.exp_ne_zero _)
    rw [hLe ζ hζ.le]
    rcases hmem with h | h
    · exact h
    · exact absurd (mem_singleton_iff.1 h) hne
  · -- boundary
    intro ζ hζ
    have hq := exp_neg_mem_sphere hζ
    obtain ⟨x, hx, hxe⟩ : f (Complex.exp (-ζ)) ∈ (fun x => (x - z)⁻¹) '' frontier K :=
      hfs ▸ mem_image_of_mem f hq
    rw [hLe ζ hζ.ge, ← hxe]
    simp only [inv_inv, add_sub_cancel]
    exact hx

end LQGMetric.CONF.DD
