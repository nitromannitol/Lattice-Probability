import Mathlib

/-!
# Continuity, compact sets and measures on the complex plane

Auxiliary facts: continuity of slices of jointly continuous families, the scaling of push-forward
measures under division by a nonzero scalar, the atom-vanishing argument under scaling, the openness of
the set of centres whose closed ball lies in an open set, a uniform radius of containment for compact
subsets of open sets, measurability of the zero-boundary circle family, continuity of products with
functions whose support lies in an open set, integrals of finite sums over compactly supported
measures, and the finiteness of a density measure on a compact set.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb.CompactSupportMeasure

/-- A slice `z ↦ h ε z` at a positive radius is continuous when `h` is continuous on `(0,∞) × ℂ`. -/
theorem continuous_slice {h : ℝ → ℂ → ℝ}
    (hh : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) {ε : ℝ} (hε : 0 < ε) :
    Continuous (h ε) := by
  have h1 : ContinuousOn (fun z : ℂ => (ε, z)) Set.univ :=
    (continuous_const.prodMk continuous_id).continuousOn
  have h2 : ContinuousOn (fun z : ℂ => h ε z) Set.univ :=
    hh.comp h1 fun z _ => ⟨hε, Set.mem_univ z⟩
  exact continuousOn_univ.mp h2

/-- The rescaled decoded measure has atom mass `c⁻¹ · μ{0}` at the origin, because `(·/R)` fixes `0`. -/
theorem smul_map_div_singleton (c : ℝ≥0∞) (ν : Measure ℂ) {R : ℝ} (hR : R ≠ 0) :
    (c • ν.map (fun x => (x - 0) / ((R : ℝ) : ℂ))) {0} = c * ν {0} := by
  have hpre : (fun x : ℂ => (x - 0) / ((R : ℝ) : ℂ)) ⁻¹' {0} = {0} := by
    ext x
    simp [hR]
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (by fun_prop) (measurableSet_singleton 0), hpre]

/-- **Fatou argument.** Let `a` be the atom mass and `b n` the atom masses of the rescaled decoded measures. They have
the same laws as `a`, and `b n = c_n⁻¹ a` with `c_n → 0`, `c_n > 0` almost surely. Then `a = 0` almost surely. -/
theorem atom_vanishing_of_scaling {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (a : Ω → ℝ≥0∞) (b : ℕ → Ω → ℝ≥0∞) (c : ℕ → Ω → ℝ)
    (ha : Measurable a)
    (hlaw : ∀ (n : ℕ) (L : ℝ≥0∞), P (b n ⁻¹' Set.Ioi L) = P (a ⁻¹' Set.Ioi L))
    (hfin : ∀ᵐ ω ∂P, a ω ≠ ⊤)
    (hscale : ∀ᵐ ω ∂P, ∀ n, b n ω = ENNReal.ofReal (c n ω)⁻¹ * a ω)
    (hc0 : ∀ᵐ ω ∂P, Tendsto (fun n => c n ω) atTop (𝓝 0))
    (hcpos : ∀ (n : ℕ) (ω : Ω), 0 < c n ω) :
    ∀ᵐ ω ∂P, a ω = 0 := by
  have key : ∀ L : ℕ, P (a ⁻¹' Set.Ioi 0) ≤ P (a ⁻¹' Set.Ioi (L : ℝ≥0∞)) := by
    intro L
    let T : ℕ → Set Ω := fun N => ⋂ n, ⋂ (_ : N ≤ n), b n ⁻¹' Set.Ioi (L : ℝ≥0∞)
    have hTmono : Monotone T := by
      intro N M hNM ω hω
      simp only [T, Set.mem_iInter] at hω ⊢
      intro n hn
      exact hω n (hNM.trans hn)
    have hcover : a ⁻¹' Set.Ioi 0 ≤ᵐ[P] ⋃ N, T N := by
      filter_upwards [hfin, hscale, hc0] with ω hfω hsω hcω
      intro hpos
      have hpos' : (0 : ℝ≥0∞) < a ω := hpos
      have h1 : Tendsto (fun n => ENNReal.ofReal (c n ω)⁻¹) atTop (𝓝 ⊤) := by
        have hinv : Tendsto (fun n => (c n ω)⁻¹) atTop atTop :=
          tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨hcω, Eventually.of_forall fun n => hcpos n ω⟩)
        exact ENNReal.tendsto_ofReal_atTop.comp hinv
      have h2 : Tendsto (fun n => b n ω) atTop (𝓝 ⊤) := by
        have hfun : (fun n => b n ω) = fun n => ENNReal.ofReal (c n ω)⁻¹ * a ω := funext hsω
        rw [hfun]
        have h3 := ENNReal.Tendsto.mul_const (b := a ω) h1 (Or.inl ENNReal.top_ne_zero)
        rwa [ENNReal.top_mul hpos'.ne'] at h3
      have h4 : ∀ᶠ n in atTop, (L : ℝ≥0∞) < b n ω :=
        h2.eventually_const_lt (ENNReal.natCast_ne_top L).lt_top
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h4
      exact Set.mem_iUnion.2 ⟨N, Set.mem_iInter.2 fun n => Set.mem_iInter.2 fun hn => hN n hn⟩
    have h1 : P (a ⁻¹' Set.Ioi 0) ≤ P (⋃ N, T N) := measure_mono_ae hcover
    have h2 : Tendsto (fun N => P (T N)) atTop (𝓝 (P (⋃ N, T N))) :=
      tendsto_measure_iUnion_atTop (fun N M hNM => hTmono hNM)
    have h3 : ∀ N, P (T N) ≤ P (a ⁻¹' Set.Ioi (L : ℝ≥0∞)) := fun N =>
      (measure_mono (fun ω hω => Set.mem_iInter.1 (Set.mem_iInter.1 hω N) le_rfl)).trans (hlaw N L).le
    have h4 : P (⋃ N, T N) ≤ P (a ⁻¹' Set.Ioi (L : ℝ≥0∞)) := le_of_tendsto h2 (Eventually.of_forall h3)
    exact h1.trans h4
  have hS : Antitone (fun L : ℕ => a ⁻¹' Set.Ioi (L : ℝ≥0∞)) := by
    intro L M hLM
    exact Set.preimage_mono (Set.Ioi_subset_Ioi (by exact_mod_cast hLM))
  have hlim := tendsto_measure_iInter_atTop (μ := P) (s := fun L : ℕ => a ⁻¹' Set.Ioi (L : ℝ≥0∞))
    (fun L : ℕ => (ha measurableSet_Ioi).nullMeasurableSet) hS ⟨0, measure_ne_top P _⟩
  have hinter : P (⋂ L : ℕ, a ⁻¹' Set.Ioi (L : ℝ≥0∞)) = 0 := by
    apply measure_mono_null (t := {ω | ¬ a ω ≠ ⊤})
    · intro ω hω
      rw [Set.mem_iInter] at hω
      show ¬ a ω ≠ ⊤
      intro hne
      obtain ⟨L, hL⟩ := ENNReal.exists_nat_gt hne
      exact absurd (hω L) (not_lt.2 hL.le)
    · exact ae_iff.1 hfin
  have hzero : P (a ⁻¹' Set.Ioi 0) = 0 := by
    have hle := ge_of_tendsto hlim (Eventually.of_forall key)
    rw [hinter] at hle
    exact nonpos_iff_eq_zero.1 hle
  have hz : P {ω | ¬ a ω = 0} = 0 :=
    measure_mono_null (fun ω hω => pos_iff_ne_zero.2 hω) hzero
  exact ae_iff.2 hz

/-- The set of centres whose closed `ε`-ball lies in the open set `D` is open. -/
theorem isOpen_setOf_closedBall_subset {D : Set ℂ} (hD : IsOpen D) {ε : ℝ} (hε : 0 ≤ ε) :
    IsOpen {z : ℂ | Metric.closedBall z ε ⊆ D} := by
  rw [Metric.isOpen_iff]
  intro z hz
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall z ε).exists_cthickening_subset_open hD hz
  rw [cthickening_closedBall hδ.le hε] at hsub
  refine ⟨δ, hδ, fun z' hz' w hw => hsub ?_⟩
  rw [Metric.mem_closedBall]
  have h1 : dist w z' ≤ ε := Metric.mem_closedBall.mp hw
  have h2 : dist z' z < δ := Metric.mem_ball.mp hz'
  calc dist w z ≤ dist w z' + dist z' z := dist_triangle _ _ _
    _ ≤ δ + ε := by linarith

/-- Uniform admissibility on a compact set: for `K ⊆ D` compact, `D` open, small closed balls around `K` lie in `D`. -/
theorem exists_closedBall_subset_of_compact {D K : Set ℂ} (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, ∀ ε : ℝ, 0 ≤ ε → ε < δ → Metric.closedBall z ε ⊆ D := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hD hKD
  refine ⟨δ, hδ, fun z hz ε hε hεδ w hw => hsub ?_⟩
  exact Metric.mem_cthickening_of_dist_le w z δ K hz (by
    have := Metric.mem_closedBall.mp hw
    linarith)

/-- Measurability in `z` of a zero-boundary circle average, from its continuity on admissible circles and its
vanishing on non-admissible ones (the zero-outside convention). -/
theorem measurable_zeroBoundary_circle {D : Set ℂ} (hD : IsOpen D) {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → ℂ → ℝ} (hzero : ∀ r z, ¬ Metric.closedBall z r ⊆ D → g r z = 0)
    (hcont : ContinuousOn (fun p : ℝ × ℂ => g p.1 p.2) {p | 0 < p.1 ∧ Metric.closedBall p.2 p.1 ⊆ D}) :
    Measurable (g ε) := by
  classical
  have hAo := isOpen_setOf_closedBall_subset hD hε.le
  have hmap : Continuous fun z : ℂ => ((ε, z) : ℝ × ℂ) := continuous_const.prodMk continuous_id
  have hcA : ContinuousOn (g ε) {z : ℂ | Metric.closedBall z ε ⊆ D} :=
    hcont.comp hmap.continuousOn (fun z hz => ⟨hε, hz⟩)
  have hfun : g ε = {z : ℂ | Metric.closedBall z ε ⊆ D}.piecewise (g ε) (fun _ => 0) := by
    funext z
    by_cases hz : z ∈ {z : ℂ | Metric.closedBall z ε ⊆ D}
    · rw [Set.piecewise_eq_of_mem _ _ _ hz]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hz]
      exact hzero ε z hz
  rw [hfun]
  exact ContinuousOn.measurable_piecewise hcA continuousOn_const hAo.measurableSet

/-- Multiplying a continuous compactly supported function by a function continuous on an open set `D` that contains
its support gives a continuous function on the whole plane. -/
theorem continuous_mul_of_tsupport_subset {D : Set ℂ} (hD : IsOpen D) {f g : ℂ → ℝ} (hf : Continuous f)
    (hfD : tsupport f ⊆ D) (hg : ContinuousOn g D) : Continuous fun z => f z * g z := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ D
  · exact (hf.continuousAt).mul (hg.continuousAt (hD.mem_nhds hz))
  · have hzf : z ∉ tsupport f := fun h => hz (hfD h)
    have hev : (fun z => f z * g z) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hzf] with w hw
      simp [image_eq_zero_of_notMem_tsupport hw]
    exact continuousAt_const.congr hev.symm

/-- Linearity of an integral against a locally finite measure over a finite decomposition into continuous compactly
supported pieces. -/
theorem integral_finset_compactSupport {ν : Measure ℂ} [IsFiniteMeasureOnCompacts ν] {ι : Type} [Fintype ι]
    (φ : ι → ℂ → ℝ) (hφc : ∀ i, Continuous (φ i)) (hφs : ∀ i, HasCompactSupport (φ i)) (f : ℂ → ℝ)
    (hf : ∀ z, f z = ∑ i, φ i z) : ∫ z, f z ∂ν = ∑ i, ∫ z, φ i z ∂ν := by
  have hfe : f = fun z => ∑ i, φ i z := funext hf
  rw [hfe]
  exact integral_finsetSum _ (fun i _ => (hφc i).integrable_of_hasCompactSupport (hφs i))

/-- Finiteness on compact subsets of `D` for a density `ofReal ∘ φ` with `φ` continuous on `D` (deterministic). On a
compact `K ⊆ D` the density is bounded by `ofReal M`, `M = sup_K |φ|`, so `(μ|_D).withDensity (ofReal ∘ φ)` charges
`K` with at most `ofReal M * μ K`. No finiteness near `∂D` is claimed. -/
theorem withDensity_restrict_compact_lt_top {D K : Set ℂ} {μ : Measure ℂ} {φ : ℂ → ℝ}
    (hK : IsCompact K) (hKD : K ⊆ D) (hφ : ContinuousOn φ D) (hμK : μ K < ⊤) :
    ((μ.restrict D).withDensity fun z => ENNReal.ofReal (φ z)) K < ⊤ := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hφ.mono hKD)
  have hbound : ∀ x ∈ K, ENNReal.ofReal (φ x) ≤ ENNReal.ofReal M := fun x hx => by
    have h := hM x hx
    rw [Real.norm_eq_abs] at h
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans h)
  rw [withDensity_apply _ hK.isClosed.measurableSet]
  calc ∫⁻ z in K, ENNReal.ofReal (φ z) ∂(μ.restrict D)
      ≤ ∫⁻ _ in K, ENNReal.ofReal M ∂(μ.restrict D) :=
        setLIntegral_mono' hK.isClosed.measurableSet hbound
    _ = ENNReal.ofReal M * μ K := by
        rw [setLIntegral_const, Measure.restrict_apply hK.isClosed.measurableSet,
          Set.inter_eq_left.2 hKD]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμK

end LatticeProb.CompactSupportMeasure
