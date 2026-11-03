/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.GoodSample at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn
import LatticeProb.Bonanno.QuantumZipper.Proofs.Field.Factorization
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Good samples and the transformation rules for continuous shifts (M4-R5, M4-T1)

Blueprint `M4_BLUEPRINT.md`, §0 ("Densities at any radius", "Good sample"), nodes M4-R5 and M4-T1.

* `bdryR γ x r`, `areaR γ x r`: the approximating measures at an arbitrary radius `r > 0`,
  with densities `r^{γ²/4} e^{(γ/2) ⟨x, fc(t,r)⟩}` on `ℝ` and `r^{γ²/2} e^{γ ⟨x, fc(z,r)⟩}` on `ℍ`
  (for a regular sample, `⟨x, fc(w,r)⟩ = evalReg x (fc w r) = F_x(w,r)`).
* `IsLQGGood γ x`: `x` is regular and the approximations along the radii `a 2^{-k}` converge
  vaguely, **uniformly in `a ∈ [1,2]`** (convergence along `atTop ×ˢ 𝓟 (Icc 1 2)`, which is
  `sup_{a∈[1,2]} |∫ f dν_{a2^{-k}} − ∫ f dν| → 0`), on `ℝ` and on `ℍ`.
* On good samples `qBoundaryMeasure`/`qAreaMeasure` are these limits (`a = 1`).
* `IsLQGGood` factors through the countable coordinates (`isLQGGood_iff_reconstruct`).
* Rule (5.1): for good `x` and `φ` continuous on `Hbar`, `x + ofFun φ` is good with
  `ν = e^{γφ/2} ν_x` and `μ = e^{γφ} μ_x`; in particular for `addConst x c`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper

/-! ## Definitions -/

/-- Boundary density at radius `r`: `r^{γ²/4} e^{(γ/2) ⟨x, fc(t,r)⟩}`. -/
def bdryDens (γ : ℝ) (x : FieldSample) (r : ℝ) (t : ℝ) : ℝ :=
  r ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * evalReg x (foldedCircle (t : ℂ) r))

/-- Area density at radius `r`: `r^{γ²/2} e^{γ ⟨x, fc(z,r)⟩}`. -/
def areaDens (γ : ℝ) (x : FieldSample) (r : ℝ) (z : ℂ) : ℝ :=
  r ^ (γ ^ 2 / 2) * Real.exp (γ * evalReg x (foldedCircle z r))

/-- `ν_r(x)`: the approximating boundary measure at an arbitrary radius `r`. -/
def bdryR (γ : ℝ) (x : FieldSample) (r : ℝ) : Measure ℝ :=
  volume.withDensity fun t => ENNReal.ofReal (bdryDens γ x r t)

/-- `μ_r(x)`: the approximating area measure at an arbitrary radius `r`, on `ℍ`. -/
def areaR (γ : ℝ) (x : FieldSample) (r : ℝ) : Measure ℂ :=
  (volume.restrict H).withDensity fun z => ENNReal.ofReal (areaDens γ x r z)

/-- The index filter for the radii `a 2^{-k}`, `k → ∞`, uniformly in `a ∈ [1,2]`. -/
def goodFilter : Filter (ℕ × ℝ) := atTop ×ˢ 𝓟 (Icc 1 2)

/-- The radius `a 2^{-k}` attached to the index `(k, a)`. -/
def goodRad (i : ℕ × ℝ) : ℝ := i.2 * radius i.1

/-- `ν` is the boundary limit of `x`, uniformly over the offsets `a ∈ [1,2]`. -/
def HasBdryLimit (γ : ℝ) (x : FieldSample) (ν : Measure ℝ) : Prop :=
  IsLocallyFiniteMeasure ν ∧
    ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun i => ∫ t, f t ∂bdryR γ x (goodRad i)) goodFilter (𝓝 (∫ t, f t ∂ν))

/-- `μ` is the area limit of `x` on `ℍ`, uniformly over the offsets `a ∈ [1,2]`. -/
def HasAreaLimit (γ : ℝ) (x : FieldSample) (μ : Measure ℂ) : Prop :=
  μ Hᶜ = 0 ∧ (∀ K, IsCompact K → K ⊆ H → μ K < ⊤) ∧
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ H →
      Tendsto (fun i => ∫ z, f z ∂areaR γ x (goodRad i)) goodFilter (𝓝 (∫ z, f z ∂μ))

/-- **Good sample** (blueprint §0 / M4-R5). -/
def IsLQGGood (γ : ℝ) (x : FieldSample) : Prop :=
  IsRegularSample x ∧ (∃ ν, HasBdryLimit γ x ν) ∧ ∃ μ, HasAreaLimit γ x μ

namespace GoodSample

open RegClosure CircleFubini
open Metric (closedBall mem_closedBall)

/-! ## Local copies (the built `RegularClosure` olean predates these lemmas) -/

variable {x : FieldSample} {F : ℂ × ℝ → ℝ}

theorem gs_norm_circleMap_le (c : ℂ) (r θ : ℝ) : ‖circleMap c r θ‖ ≤ ‖c‖ + |r| := by
  calc ‖circleMap c r θ‖ = ‖c + (circleMap c r θ - c)‖ := by ring_nf
    _ ≤ ‖c‖ + ‖circleMap c r θ - c‖ := norm_add_le _ _
    _ = ‖c‖ + |r| := by rw [circleMap_sub_center, norm_circleMap_zero]

theorem gs_continuousOn_integral_fc_fun {φ : ℂ → ℝ} (hφ : ContinuousOn φ Hbar) :
    ContinuousOn (fun q : ℂ × ℝ => ∫ v, φ v ∂foldedCircle q.1 q.2) univ :=
  continuousOn_integral_fc (P := ℂ × ℝ) (S := univ) (H := fun _ v => φ v)
    (c := fun q => q.1) (r := fun q => q.2) (hφ.comp continuousOn_snd fun q hq => hq.2)
    continuousOn_fst continuousOn_snd

/-- Vanishing circle smoothing of a function continuous on `Hbar`, locally uniformly. -/
theorem gs_tluo_smooth_continuous {φ : ℂ → ℝ} (hφ : ContinuousOn φ Hbar) :
    TendstoLocallyUniformlyOn
      (fun ρ (p : ℂ × ℝ) => ∫ u, (∫ v, φ v ∂foldedCircle u ρ) ∂foldedCircle p.1 p.2)
      (fun p => ∫ v, φ v ∂foldedCircle p.1 p.2) (𝓝[>] 0) (Hbar ×ˢ Ioi 0) := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  set R := ‖x.1‖ + x.2 + 2 with hR
  have hg := continuous_comp_foldH hφ
  have huc := (isCompact_closedBall (0 : ℂ) (R + 1)).uniformContinuousOn_of_continuous
    hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc (ε / 2) (by positivity)
  set t : Set (ℂ × ℝ) := {p | ‖p.1‖ + p.2 < R} with ht_def
  have ht : t ∈ 𝓝[Hbar ×ˢ Ioi 0] x := by
    refine mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds (isOpen_lt (by fun_prop) continuous_const) ?_)
    show ‖x.1‖ + x.2 < R
    linarith
  refine ⟨t ∩ (Hbar ×ˢ Ioi 0), inter_mem ht self_mem_nhdsWithin, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ one_pos)] with ρ hρ p hp
  have hρ0 : 0 < ρ := hρ.1
  have hΦc : ContinuousOn (fun u => ∫ v, φ v ∂foldedCircle u ρ) Hbar :=
    (gs_continuousOn_integral_fc_fun hφ).comp (continuous_id.prodMk continuous_const).continuousOn
      fun _ _ => mem_univ _
  have hin : ∀ u ∈ Hbar, ‖u‖ ≤ R → |φ u - ∫ v, φ v ∂foldedCircle u ρ| ≤ ε / 2 := by
    intro u hu huR
    have key := abs_integral_fc_sub_le (g := fun _ => φ u) (g' := φ) (w := u) (w' := u) (r := ρ)
      (r' := ρ) (C := ε / 2) continuousOn_const hφ (fun θ => by
        have h1 : φ (foldH u) = φ u := by rw [foldH_of_mem' hu]
        rw [← h1]
        have hd : dist u (circleMap u ρ θ) < δ := by
          rw [dist_comm, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
            abs_of_pos hρ0]
          exact hρ.2.trans_le (min_le_left _ _)
        have hu1 : u ∈ closedBall (0 : ℂ) (R + 1) := by
          rw [mem_closedBall, dist_zero_right]; linarith
        have hu2 : circleMap u ρ θ ∈ closedBall (0 : ℂ) (R + 1) := by
          rw [mem_closedBall, dist_zero_right]
          have := gs_norm_circleMap_le u ρ θ
          rw [abs_of_pos hρ0] at this
          linarith [hρ.2.trans_le (min_le_right _ _)]
        have := hδ' _ hu1 _ hu2 hd
        rw [Real.dist_eq] at this
        exact this.le)
    simpa using key
  rw [Real.dist_eq]
  refine lt_of_le_of_lt (abs_integral_fc_sub_le (g := φ) (C := ε / 2)
    (g' := fun u => ∫ v, φ v ∂foldedCircle u ρ) hφ hΦc fun θ => ?_) (by linarith : ε / 2 < ε)
  refine hin _ (foldH_mem_Hbar' _) ?_
  rw [norm_foldH']
  have := gs_norm_circleMap_le p.1 p.2 θ
  have hp2 : 0 < p.2 := hp.2.2
  rw [abs_of_pos hp2] at this
  have := hp.1
  simp only [ht_def, mem_setOf_eq] at this
  linarith

/-- Adding a deterministic function continuous on `Hbar` preserves regularity. -/
theorem gs_add_ofFun (h : IsRegularWith x F) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Hbar) :
    IsRegularWith (x + ofFun φ) (fun q => F q + ∫ v, φ v ∂foldedCircle q.1 q.2) := by
  have hΦ := (gs_continuousOn_integral_fc_fun hφ).mono (subset_univ (Hbar ×ˢ Ioi (0 : ℝ)))
  refine ⟨h.1.add hΦ, fun k z hz => ?_, ?_⟩
  · exact (h.2.1 k z hz).add (tendsto_of_eval_eq (y := ofFun φ) hΦ (fun d _ r _ => rfl) k hz)
  · refine tluo_of_dist_le (tluo_add h.2.2 (gs_tluo_smooth_continuous hφ)) ?_
    filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ) q hq
    have hΦc : ContinuousOn (fun u => ∫ v, φ v ∂foldedCircle u ρ) Hbar :=
      (gs_continuousOn_integral_fc_fun hφ).comp (continuous_id.prodMk continuous_const).continuousOn
        fun _ _ => mem_univ _
    rw [integral_add (integrable_fc (continuousOn_slice h.1 hρ) _ hq.2.le)
      (integrable_fc hΦc _ hq.2.le)]

theorem gs_add_ofFun_sample (h : IsRegularSample x) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Hbar) : IsRegularSample (x + ofFun φ) :=
  let ⟨_, hF⟩ := h; ⟨_, gs_add_ofFun hF hφ⟩

/-! ## Generic analysis lemmas -/

section Generic

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem integral_withDensity_ofReal {μ : Measure X} {d : X → ℝ} (hd : Measurable d)
    (h0 : ∀ t, 0 ≤ d t) (g : X → ℝ) :
    ∫ t, g t ∂μ.withDensity (fun t => ENNReal.ofReal (d t)) = ∫ t, d t * g t ∂μ := by
  have := integral_withDensity_eq_integral_smul (μ := μ) (f := fun t => (d t).toNNReal)
    hd.real_toNNReal g
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (h0 _), smul_eq_mul] at this
  exact this

theorem withDensity_lt_top {μ : Measure X} {K : Set X} (hK : IsCompact K) (hμK : μ K < ⊤)
    {d : X → ℝ} (hd : ContinuousOn d K) :
    μ.withDensity (fun t => ENNReal.ofReal (d t)) K < ⊤ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hd
  rw [withDensity_apply _ hK.isClosed.measurableSet]
  calc ∫⁻ t in K, ENNReal.ofReal (d t) ∂μ ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂μ :=
        setLIntegral_mono measurable_const fun t ht =>
          ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by simpa using hC t ht))
    _ = ENNReal.ofReal C * μ K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμK

theorem integrable_of_tsupport {μ : Measure X} {U : Set X}
    (hfin : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤) {h : X → ℝ} (hh : Continuous h)
    (hhc : HasCompactSupport h) (hhU : tsupport h ⊆ U) : Integrable h μ := by
  obtain ⟨C, hC⟩ := hh.bounded_above_of_compact_support hhc
  have : IntegrableOn h (tsupport h) μ :=
    Measure.integrableOn_of_bounded (hfin _ hhc hhU).ne hh.aestronglyMeasurable
      (ae_of_all _ hC)
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport h)).1 this

theorem exists_bump {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ g : X → ℝ, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧ EqOn g 1 K ∧
      ∀ t, 0 ≤ g t := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨g, hg1, hg0, hgc, hg01⟩ := exists_continuous_one_zero_of_isCompact hK
    isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.2 hKL)
  refine ⟨g, g.continuous, hgc, ?_, hg1, fun t => (hg01 t).1⟩
  have hs : Function.support g ⊆ interior L := fun t ht => by
    by_contra h
    exact ht (hg0 h)
  exact (closure_mono hs).trans ((closure_mono interior_subset).trans
    (hL.isClosed.closure_subset)) |>.trans hLU

/-- **Vague convergence survives locally uniformly convergent exponential weights.** -/
theorem tendsto_integral_exp_mul {ι : Type*} {L : Filter ι} {U : Set X} (hU : IsOpen U)
    {νs : ι → Measure X} {ν : Measure X}
    (hfin : ∀ᶠ i in L, ∀ K, IsCompact K → K ⊆ U → νs i K < ⊤)
    (hν : ∀ f : X → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
      Tendsto (fun i => ∫ t, f t ∂νs i) L (𝓝 (∫ t, f t ∂ν)))
    {v : ι → X → ℝ} {v0 : X → ℝ} (hv0 : ContinuousOn v0 U)
    (hvc : ∀ᶠ i in L, ContinuousOn (v i) U)
    (hv : ∀ K, IsCompact K → K ⊆ U → ∀ ε > 0, ∀ᶠ i in L, ∀ t ∈ K, |v i t - v0 t| < ε)
    {f : X → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    Tendsto (fun i => ∫ t, Real.exp (v i t) * f t ∂νs i) L
      (𝓝 (∫ t, Real.exp (v0 t) * f t ∂ν)) := by
  set K := tsupport f with hK_def
  have hK : IsCompact K := hfc
  set w : X → ℝ := fun t => Real.exp (v0 t) * f t with hw_def
  have hwc : Continuous w := ContinuousOn.continuous_of_tsupport_subset
    (hv0.rexp.mul hf.continuousOn) hU ((tsupport_mul_subset_right).trans hfU)
  have hwcs : HasCompactSupport w := hfc.mul_left
  have hwU : tsupport w ⊆ U := (tsupport_mul_subset_right).trans hfU
  have hA := hν w hwc hwcs hwU
  obtain ⟨g, hgc, hgcs, hgU, hg1, hg0⟩ := exists_bump hK hU hfU
  have hG := hν g hgc hgcs hgU
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hv0.rexp.mono hfU)
  set Bp := max B 0
  set Mp := max M 0
  set G := ∫ t, g t ∂ν
  -- the error term
  have hD : Tendsto (fun i => ∫ t, Real.exp (v i t) * f t ∂νs i - ∫ t, w t ∂νs i) L (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set C := 2 * Bp * Mp * (|G| + 1)
    have hC0 : 0 ≤ C := by positivity
    set δ := min 1 (ε / (C + 1))
    have hδ0 : 0 < δ := lt_min one_pos (by positivity)
    have hCδ : C * δ < ε := by
      calc C * δ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC0
        _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
    have hGev : ∀ᶠ i in L, ∫ t, g t ∂νs i < |G| + 1 :=
      (hG.eventually (gt_mem_nhds (show G < |G| + 1 by linarith [le_abs_self G])))
    filter_upwards [hfin, hvc, hv K hK hfU δ hδ0, hGev] with i hfi hvci hvi hGi
    have hI1 : Integrable (fun t => Real.exp (v i t) * f t) (νs i) :=
      integrable_of_tsupport hfi (ContinuousOn.continuous_of_tsupport_subset
        (hvci.rexp.mul hf.continuousOn) hU ((tsupport_mul_subset_right).trans hfU))
        hfc.mul_left ((tsupport_mul_subset_right).trans hfU)
    have hI2 : Integrable w (νs i) := integrable_of_tsupport hfi hwc hwcs hwU
    have hIg : Integrable g (νs i) := integrable_of_tsupport hfi hgc hgcs hgU
    rw [Real.dist_eq, sub_zero, ← integral_sub hI1 hI2]
    have hpt : ∀ t, ‖Real.exp (v i t) * f t - w t‖ ≤ (2 * Bp * δ * Mp) * g t := by
      intro t
      by_cases ht : t ∈ K
      · rw [hg1 ht, Pi.one_apply, mul_one, hw_def, ← sub_mul, Real.norm_eq_abs, abs_mul]
        have h1 : |v i t - v0 t| ≤ 1 := (hvi t ht).le.trans (min_le_left _ _)
        have e : Real.exp (v i t) - Real.exp (v0 t) =
            Real.exp (v0 t) * (Real.exp (v i t - v0 t) - 1) := by
          rw [mul_sub, ← Real.exp_add, mul_one]; ring_nf
        have hb1 : |Real.exp (v i t) - Real.exp (v0 t)| ≤ Bp * (2 * δ) := by
          rw [e, abs_mul]
          refine mul_le_mul ?_ ((Real.abs_exp_sub_one_le h1).trans ?_) (abs_nonneg _)
            (le_max_right _ _)
          · exact (by simpa using hB t ht : |Real.exp (v0 t)| ≤ B).trans (le_max_left _ _)
          · linarith [hvi t ht]
        have hb2 : |f t| ≤ Mp := (by simpa using hM t : |f t| ≤ M).trans (le_max_left _ _)
        calc |Real.exp (v i t) - Real.exp (v0 t)| * |f t| ≤ (Bp * (2 * δ)) * Mp :=
              mul_le_mul hb1 hb2 (abs_nonneg _) (by positivity)
          _ = 2 * Bp * δ * Mp := by ring
      · have hf0 : f t = 0 := image_eq_zero_of_notMem_tsupport ht
        simp only [hw_def, hf0, mul_zero, sub_zero, norm_zero]
        exact mul_nonneg (by positivity) (hg0 t)
    calc ‖∫ t, (Real.exp (v i t) * f t - w t) ∂νs i‖
        ≤ ∫ t, (2 * Bp * δ * Mp) * g t ∂νs i :=
          norm_integral_le_of_norm_le (hIg.const_mul _) (ae_of_all _ hpt)
      _ = (2 * Bp * δ * Mp) * ∫ t, g t ∂νs i := integral_const_mul _ _
      _ ≤ (2 * Bp * δ * Mp) * (|G| + 1) := mul_le_mul_of_nonneg_left hGi.le (by positivity)
      _ = C * δ := by ring
      _ < ε := hCδ
  have := hD.add hA
  rw [zero_add] at this
  refine this.congr fun i => ?_
  simp only [hw_def]
  ring

end Generic

/-! ## Vanishing smoothing of continuous functions, uniformly on compacts -/

theorem smooth_unif {φ : ℂ → ℝ} (hφ : ContinuousOn φ Hbar) {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ Hbar) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ w ∈ K, |∫ v, φ v ∂foldedCircle w r - φ w| < ε := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hg := continuous_comp_foldH hφ
  have huc := (isCompact_closedBall (0 : ℂ) (|R| + 1)).uniformContinuousOn_of_continuous
    hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc (ε / 2) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ one_pos)] with r hr w hw
  have hr0 : 0 < r := hr.1
  have hwH := hKH hw
  have key := abs_integral_fc_sub_le (g := φ) (g' := fun _ => φ w) (w := w) (w' := w) (r := r)
    (r' := r) (C := ε / 2) hφ continuousOn_const (fun θ => by
      have h1 : φ (foldH w) = φ w := by rw [foldH_of_mem' hwH]
      show |φ (foldH (circleMap w r θ)) - φ w| ≤ ε / 2
      rw [← h1]
      have hd : dist (circleMap w r θ) w < δ := by
        rw [dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr0]
        exact hr.2.trans_le (min_le_left _ _)
      have hw1 : w ∈ Metric.closedBall (0 : ℂ) (|R| + 1) := by
        rw [Metric.mem_closedBall, dist_zero_right]; linarith [hR w hw, le_abs_self R]
      have hw2 : circleMap w r θ ∈ Metric.closedBall (0 : ℂ) (|R| + 1) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        have := gs_norm_circleMap_le w r θ
        rw [abs_of_pos hr0] at this
        linarith [hR w hw, le_abs_self R, hr.2.trans_le (min_le_right _ _)]
      have := hδ' _ hw2 _ hw1 hd
      rw [Real.dist_eq] at this
      exact this.le)
  rw [integral_const, probReal_univ, one_smul] at key
  linarith

theorem tendsto_goodRad : Tendsto goodRad goodFilter (𝓝[>] 0) := by
  have hsnd : ∀ᶠ i in goodFilter, i.2 ∈ Icc (1 : ℝ) 2 :=
    tendsto_snd.eventually (eventually_principal.2 fun _ h => h)
  have hrad : Tendsto (fun i : ℕ × ℝ => radius i.1) goodFilter (𝓝 0) :=
    (tendsto_nhdsWithin_iff.1 tendsto_radius_nhdsGT).1.comp tendsto_fst
  refine tendsto_nhdsWithin_iff.2 ⟨?_, hsnd.mono fun i hi => ?_⟩
  · have h2 := hrad.const_mul 2
    rw [mul_zero] at h2
    refine squeeze_zero' (hsnd.mono fun i hi => ?_) (hsnd.mono fun i hi => ?_) h2
    · exact mul_nonneg (by linarith [hi.1]) (radius_pos _).le
    · exact mul_le_mul_of_nonneg_right hi.2 (radius_pos _).le
  · exact mul_pos (by linarith [hi.1]) (radius_pos _)

theorem eventually_goodRad_pos : ∀ᶠ i in goodFilter, 0 < goodRad i :=
  tendsto_goodRad.eventually self_mem_nhdsWithin

/-! ## Regular samples: densities -/

theorem continuous_evalReg_fc (h : IsRegularWith x F) {r : ℝ} (hr : 0 < r) :
    Continuous fun z : ℂ => evalReg x (foldedCircle z r) := by
  have e : (fun z : ℂ => evalReg x (foldedCircle z r)) = fun z => F (foldH z, r) :=
    funext fun z => h.evalReg_fc z hr
  rw [e]
  exact (continuousOn_slice h.1 hr).comp_continuous continuous_foldH' foldH_mem_Hbar'

theorem continuous_bdryDens (γ : ℝ) (h : IsRegularWith x F) {r : ℝ} (hr : 0 < r) :
    Continuous (bdryDens γ x r) :=
  continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
    ((continuous_evalReg_fc h hr).comp Complex.continuous_ofReal)))

theorem continuous_areaDens (γ : ℝ) (h : IsRegularWith x F) {r : ℝ} (hr : 0 < r) :
    Continuous (areaDens γ x r) :=
  continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
    (continuous_evalReg_fc h hr)))

theorem bdryDens_nonneg (γ : ℝ) (x : FieldSample) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    0 ≤ bdryDens γ x r t :=
  mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le

theorem areaDens_nonneg (γ : ℝ) (x : FieldSample) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    0 ≤ areaDens γ x r z :=
  mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le

theorem bdryR_lt_top (γ : ℝ) (h : IsRegularWith x F) {r : ℝ} (hr : 0 < r) {K : Set ℝ}
    (hK : IsCompact K) : bdryR γ x r K < ⊤ :=
  withDensity_lt_top hK hK.measure_lt_top (continuous_bdryDens γ h hr).continuousOn

theorem areaR_lt_top (γ : ℝ) (h : IsRegularWith x F) {r : ℝ} (hr : 0 < r) {K : Set ℂ}
    (hK : IsCompact K) : areaR γ x r K < ⊤ :=
  withDensity_lt_top hK ((Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top)
    (continuous_areaDens γ h hr).continuousOn

theorem bdryR_radius (γ : ℝ) (h : IsRegularWith x F) (k : ℕ) :
    bdryR γ x (1 * radius k) = bdryApprox γ x k := by
  rw [one_mul, bdryR, bdryApprox]
  congr 1
  funext t
  have ht : (t : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (t : ℂ).im by simp
  rw [bdryDens, h.evalReg_fc_of_mem ht (radius_pos k), h.avgReg_eq k ht]

theorem areaR_radius (γ : ℝ) (h : IsRegularWith x F) (k : ℕ) :
    areaR γ x (1 * radius k) = areaApprox γ x k := by
  rw [one_mul, areaR, areaApprox]
  refine withDensity_congr_ae ((ae_restrict_mem isOpen_H.measurableSet).mono fun z hz => ?_)
  have hz' : z ∈ Hbar := show (0:ℝ) ≤ z.im from le_of_lt hz
  show ENNReal.ofReal (areaDens γ x (radius k) z) = ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg x k z))
  rw [areaDens, h.evalReg_fc_of_mem hz' (radius_pos k), h.avgReg_eq k hz']

theorem tendsto_one_goodFilter : Tendsto (fun k : ℕ => (k, (1 : ℝ))) atTop goodFilter :=
  tendsto_id.prodMk (tendsto_principal.2 (Eventually.of_forall fun _ => ⟨le_rfl, one_le_two⟩))

/-- On a good sample the boundary limit is `qBoundaryMeasure`. -/
theorem qBoundaryMeasure_eq_of_hasBdryLimit {γ : ℝ} (hx : IsRegularSample x) {ν : Measure ℝ}
    (hν : HasBdryLimit γ x ν) : qBoundaryMeasure γ x = ν := by
  obtain ⟨F, hF⟩ := hx
  refine qBoundaryMeasure_eq ⟨hν.1, fun f hf hfc => ?_⟩
  have := (hν.2 f hf hfc).comp tendsto_one_goodFilter
  refine this.congr fun k => ?_
  simp only [Function.comp, goodRad, bdryR_radius γ hF]

/-- On a good sample the area limit is `qAreaMeasure`. -/
theorem qAreaMeasure_eq_of_hasAreaLimit {γ : ℝ} (hx : IsRegularSample x) {μ : Measure ℂ}
    (hμ : HasAreaLimit γ x μ) : qAreaMeasure γ x = μ := by
  obtain ⟨F, hF⟩ := hx
  refine qAreaMeasure_eq ⟨hμ.1, hμ.2.1, fun f hf hfc hfU => ?_⟩
  have := (hμ.2.2 f hf hfc hfU).comp tendsto_one_goodFilter
  refine this.congr fun k => ?_
  simp only [Function.comp, goodRad, areaR_radius γ hF]

theorem _root_.QuantumZipper.IsLQGGood.qBoundaryMeasure_spec {γ : ℝ} (hx : IsLQGGood γ x) :
    HasBdryLimit γ x (qBoundaryMeasure γ x) := by
  obtain ⟨hr, ⟨ν, hν⟩, _⟩ := hx
  rwa [qBoundaryMeasure_eq_of_hasBdryLimit hr hν]

theorem _root_.QuantumZipper.IsLQGGood.qAreaMeasure_spec {γ : ℝ} (hx : IsLQGGood γ x) :
    HasAreaLimit γ x (qAreaMeasure γ x) := by
  obtain ⟨hr, _, ⟨μ, hμ⟩⟩ := hx
  rwa [qAreaMeasure_eq_of_hasAreaLimit hr hμ]

/-! ## Factorization through the countable coordinates (M4-R5(a), first half) -/

open Factorization in
theorem reconstruct_coords_fc (x : FieldSample) (n k : ℕ) (z : ℂ) :
    reconstruct (coords x) (foldedCircle (dyadicRoundC n z) (radius k)) =
      x (foldedCircle (dyadicRoundC n z) (radius k)) := by
  obtain ⟨i, hi⟩ := dyadicIndex_surj n k z
  have := reconstruct_coords_apply x i
  simp only [hi] at this
  exact this

open Factorization in
theorem isRegularWith_reconstruct_iff (x : FieldSample) (F : ℂ × ℝ → ℝ) :
    IsRegularWith (reconstruct (coords x)) F ↔ IsRegularWith x F := by
  unfold IsRegularWith
  simp only [reconstruct_coords_fc]

open Factorization in
/-- `IsLQGGood γ x` only depends on the countable coordinates `coords x`. -/
theorem isLQGGood_iff_reconstruct (γ : ℝ) (x : FieldSample) :
    IsLQGGood γ (reconstruct (coords x)) ↔ IsLQGGood γ x := by
  have he := evalReg_congr (avgReg_reconstruct_coords x)
  have hb : bdryR γ (reconstruct (coords x)) = bdryR γ x := by
    funext r; simp only [bdryR, bdryDens, he]
  have ha : areaR γ (reconstruct (coords x)) = areaR γ x := by
    funext r; simp only [areaR, areaDens, he]
  simp only [IsLQGGood, IsRegularSample, isRegularWith_reconstruct_iff, HasBdryLimit,
    HasAreaLimit, hb, ha]

/-! ## Rule (5.1): adding a continuous function -/

/-- Smoothed values `Φ(w, r) = ∫ φ d fc(w, r)`. -/
def smoothFun (φ : ℂ → ℝ) (w : ℂ) (r : ℝ) : ℝ := ∫ v, φ v ∂foldedCircle w r

theorem continuous_smoothFun {φ : ℂ → ℝ} (hφ : ContinuousOn φ Hbar) (r : ℝ) :
    Continuous fun w => smoothFun φ w r :=
  continuousOn_univ.1 ((gs_continuousOn_integral_fc_fun hφ).comp
    (continuous_id.prodMk continuous_const).continuousOn fun _ _ => mem_univ _)

theorem evalReg_add_ofFun_fc (h : IsRegularWith x F) {φ : ℂ → ℝ} (hφ : ContinuousOn φ Hbar)
    {w : ℂ} (hw : w ∈ Hbar) {r : ℝ} (hr : 0 < r) :
    evalReg (x + ofFun φ) (foldedCircle w r) =
      evalReg x (foldedCircle w r) + smoothFun φ w r := by
  rw [(gs_add_ofFun h hφ).evalReg_fc_of_mem hw hr, h.evalReg_fc_of_mem hw hr]
  rfl

theorem integral_bdryR_add_ofFun (γ : ℝ) (h : IsRegularWith x F) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Hbar) {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ) :
    ∫ t, f t ∂bdryR γ (x + ofFun φ) r =
      ∫ t, Real.exp (γ / 2 * smoothFun φ t r) * f t ∂bdryR γ x r := by
  have h' := gs_add_ofFun h hφ
  rw [bdryR, bdryR, integral_withDensity_ofReal (continuous_bdryDens γ h' hr).measurable
    (bdryDens_nonneg γ _ hr), integral_withDensity_ofReal (continuous_bdryDens γ h hr).measurable
    (bdryDens_nonneg γ _ hr)]
  congr 1
  funext t
  have ht : (t : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (t : ℂ).im by simp
  rw [bdryDens, bdryDens, evalReg_add_ofFun_fc h hφ ht hr, mul_add, Real.exp_add]
  ring

theorem integral_areaR_add_ofFun (γ : ℝ) (h : IsRegularWith x F) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Hbar) {r : ℝ} (hr : 0 < r) (f : ℂ → ℝ) :
    ∫ z, f z ∂areaR γ (x + ofFun φ) r =
      ∫ z, Real.exp (γ * smoothFun φ z r) * f z ∂areaR γ x r := by
  have h' := gs_add_ofFun h hφ
  rw [areaR, areaR, integral_withDensity_ofReal (continuous_areaDens γ h' hr).measurable
    (areaDens_nonneg γ _ hr), integral_withDensity_ofReal (continuous_areaDens γ h hr).measurable
    (areaDens_nonneg γ _ hr)]
  refine integral_congr_ae ((ae_restrict_mem isOpen_H.measurableSet).mono fun z hz => ?_)
  have hz' : z ∈ Hbar := show (0:ℝ) ≤ z.im from le_of_lt hz
  simp only
  rw [areaDens, areaDens, evalReg_add_ofFun_fc h hφ hz' hr, mul_add, Real.exp_add]
  ring

/-- Uniform convergence of `c Φ(·, goodRad i)` to `c φ` on compacts of `Hbar`. -/
theorem smooth_unif_good {φ : ℂ → ℝ} (hφ : ContinuousOn φ Hbar) (c : ℝ) {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ Hbar) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in goodFilter, ∀ w ∈ K, |c * smoothFun φ w (goodRad i) - c * φ w| < ε := by
  have := tendsto_goodRad.eventually (smooth_unif hφ hK hKH (ε / (|c| + 1)) (by positivity))
  filter_upwards [this] with i hi w hw
  rw [← mul_sub, abs_mul]
  calc |c| * |smoothFun φ w (goodRad i) - φ w| ≤ |c| * (ε / (|c| + 1)) :=
        mul_le_mul_of_nonneg_left (hi w hw).le (abs_nonneg _)
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg c]

theorem continuous_ofReal_comp {φ : ℂ → ℝ} (hφ : ContinuousOn φ Hbar) :
    Continuous fun t : ℝ => φ t :=
  hφ.comp_continuous Complex.continuous_ofReal fun t => show (0 : ℝ) ≤ (t : ℂ).im by simp

/-- **Rule (5.1), boundary.** -/
theorem hasBdryLimit_add_ofFun {γ : ℝ} (hx : IsRegularSample x) {ν : Measure ℝ}
    (hν : HasBdryLimit γ x ν) {φ : ℂ → ℝ} (hφ : ContinuousOn φ Hbar) :
    HasBdryLimit γ (x + ofFun φ)
      (ν.withDensity fun t => ENNReal.ofReal (Real.exp (γ / 2 * φ t))) := by
  obtain ⟨F, hF⟩ := hx
  have hφr := continuous_ofReal_comp hφ
  have hdc : Continuous fun t : ℝ => Real.exp (γ / 2 * φ t) :=
    Real.continuous_exp.comp (continuous_const.mul hφr)
  have := hν.1
  refine ⟨?_, fun f hf hfc => ?_⟩
  · have : IsFiniteMeasureOnCompacts
        (ν.withDensity fun t => ENNReal.ofReal (Real.exp (γ / 2 * φ t))) :=
      ⟨fun K hK => withDensity_lt_top hK hK.measure_lt_top hdc.continuousOn⟩
    infer_instance
  rw [integral_withDensity_ofReal hdc.measurable fun _ => (Real.exp_pos _).le]
  have key := tendsto_integral_exp_mul (X := ℝ) (L := goodFilter) (U := univ) isOpen_univ
    (νs := fun i => bdryR γ x (goodRad i)) (ν := ν)
    (eventually_goodRad_pos.mono fun i hi K hK _ => bdryR_lt_top γ hF hi hK)
    (fun g hg hgc _ => hν.2 g hg hgc)
    (v := fun i t => γ / 2 * smoothFun φ t (goodRad i)) (v0 := fun t => γ / 2 * φ t)
    (continuous_const.mul hφr).continuousOn
    (Eventually.of_forall fun i => (continuous_const.mul
      ((continuous_smoothFun hφ _).comp Complex.continuous_ofReal)).continuousOn)
    (fun K hK _ ε hε => by
      have := smooth_unif_good hφ (γ / 2) (hK.image Complex.continuous_ofReal)
        (fun _ ⟨t, _, ht⟩ => ht ▸ show (0 : ℝ) ≤ (t : ℂ).im by simp) ε hε
      filter_upwards [this] with i hi t ht
      exact hi _ ⟨t, ht, rfl⟩)
    hf hfc (subset_univ _)
  refine key.congr' (eventually_goodRad_pos.mono fun i hi => ?_)
  exact (integral_bdryR_add_ofFun γ hF hφ hi f).symm

theorem ae_Hbar_of_null {μ : Measure ℂ} (h : μ Hᶜ = 0) : ∀ᵐ z ∂μ, z ∈ H :=
  measure_eq_zero_iff_ae_notMem.1 h |>.mono fun _ hz => by simpa using hz

/-- **Rule (5.1), area.** -/
theorem hasAreaLimit_add_ofFun {γ : ℝ} (hx : IsRegularSample x) {μ : Measure ℂ}
    (hμ : HasAreaLimit γ x μ) {φ : ℂ → ℝ} (hφ : ContinuousOn φ Hbar) :
    HasAreaLimit γ (x + ofFun φ)
      (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * φ z))) := by
  obtain ⟨F, hF⟩ := hx
  have hφf : Continuous fun z => φ (foldH z) := continuous_comp_foldH hφ
  have hdc : Continuous fun z => Real.exp (γ * φ (foldH z)) :=
    Real.continuous_exp.comp (continuous_const.mul hφf)
  have hae : ∀ᵐ z ∂μ, z ∈ H := ae_Hbar_of_null hμ.1
  have heq : (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * φ z))) =
      μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * φ (foldH z))) :=
    withDensity_congr_ae (hae.mono fun z hz => by
      simp only [foldH_of_mem' (show (0:ℝ) ≤ z.im from le_of_lt hz)])
  rw [heq]
  refine ⟨?_, fun K hK hKH => withDensity_lt_top hK (hμ.2.1 K hK hKH) hdc.continuousOn,
    fun f hf hfc hfU => ?_⟩
  · exact withDensity_absolutelyContinuous _ _ hμ.1
  rw [integral_withDensity_ofReal hdc.measurable fun _ => (Real.exp_pos _).le]
  have key := tendsto_integral_exp_mul (X := ℂ) (L := goodFilter) (U := H) isOpen_H
    (νs := fun i => areaR γ x (goodRad i)) (ν := μ)
    (eventually_goodRad_pos.mono fun i hi K hK _ => areaR_lt_top γ hF hi hK)
    (fun g hg hgc hgU => hμ.2.2 g hg hgc hgU)
    (v := fun i z => γ * smoothFun φ z (goodRad i)) (v0 := fun z => γ * φ (foldH z))
    (continuous_const.mul hφf).continuousOn
    (Eventually.of_forall fun i => (continuous_const.mul
      (continuous_smoothFun hφ _)).continuousOn)
    (fun K hK hKH ε hε => by
      have := smooth_unif_good hφ γ hK (fun z hz => show (0:ℝ) ≤ z.im from le_of_lt (hKH hz)) ε hε
      filter_upwards [this] with i hi z hz
      rw [foldH_of_mem' (show (0:ℝ) ≤ z.im from le_of_lt (hKH hz))]
      exact hi z hz)
    hf hfc hfU
  refine key.congr' (eventually_goodRad_pos.mono fun i hi => ?_)
  exact (integral_areaR_add_ofFun γ hF hφ hi f).symm

/-- **M4-T1, continuous functions.** For good `x` and `φ` continuous on `Hbar`, the sample
`x + ofFun φ` is good. -/
theorem _root_.QuantumZipper.IsLQGGood.add_ofFun {γ : ℝ} (hx : IsLQGGood γ x) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Hbar) : IsLQGGood γ (x + ofFun φ) :=
  ⟨gs_add_ofFun_sample hx.1 hφ, ⟨_, hasBdryLimit_add_ofFun hx.1 hx.qBoundaryMeasure_spec hφ⟩,
    ⟨_, hasAreaLimit_add_ofFun hx.1 hx.qAreaMeasure_spec hφ⟩⟩

/-- **M4-T1**, boundary: `ν_{x + φ} = e^{γφ/2} ν_x`. -/
theorem qBoundaryMeasure_add_ofFun {γ : ℝ} (hx : IsLQGGood γ x) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Hbar) :
    qBoundaryMeasure γ (x + ofFun φ) =
      (qBoundaryMeasure γ x).withDensity fun t => ENNReal.ofReal (Real.exp (γ / 2 * φ t)) :=
  qBoundaryMeasure_eq_of_hasBdryLimit (gs_add_ofFun_sample hx.1 hφ)
    (hasBdryLimit_add_ofFun hx.1 hx.qBoundaryMeasure_spec hφ)

/-- **M4-T1**, area: `μ_{x + φ} = e^{γφ} μ_x`. -/
theorem qAreaMeasure_add_ofFun {γ : ℝ} (hx : IsLQGGood γ x) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Hbar) :
    qAreaMeasure γ (x + ofFun φ) =
      (qAreaMeasure γ x).withDensity fun z => ENNReal.ofReal (Real.exp (γ * φ z)) :=
  qAreaMeasure_eq_of_hasAreaLimit (gs_add_ofFun_sample hx.1 hφ)
    (hasAreaLimit_add_ofFun hx.1 hx.qAreaMeasure_spec hφ)

/-! ## Additive constants -/

theorem addConst_eq_add_ofFun (x : FieldSample) (c : ℝ) :
    addConst x c = x + ofFun (fun _ => c) := by
  funext μ
  simp only [addConst, ofFun, Pi.add_apply, integral_const, smul_eq_mul, Measure.real]
  ring

theorem _root_.QuantumZipper.IsLQGGood.addConst {γ : ℝ} (hx : IsLQGGood γ x) (c : ℝ) :
    IsLQGGood γ (addConst x c) := by
  rw [addConst_eq_add_ofFun]; exact hx.add_ofFun continuousOn_const

/-- **M4-T1**, constants, boundary: `ν_{x + c} = e^{γc/2} ν_x`. -/
theorem qBoundaryMeasure_addConst {γ : ℝ} (hx : IsLQGGood γ x) (c : ℝ) :
    qBoundaryMeasure γ (addConst x c) = ENNReal.ofReal (Real.exp (γ * c / 2)) •
      qBoundaryMeasure γ x := by
  rw [addConst_eq_add_ofFun, qBoundaryMeasure_add_ofFun hx continuousOn_const,
    withDensity_const]
  congr 3
  ring

/-- **M4-T1**, constants, area: `μ_{x + c} = e^{γc} μ_x`. -/
theorem qAreaMeasure_addConst {γ : ℝ} (hx : IsLQGGood γ x) (c : ℝ) :
    qAreaMeasure γ (addConst x c) = ENNReal.ofReal (Real.exp (γ * c)) • qAreaMeasure γ x := by
  rw [addConst_eq_add_ofFun, qAreaMeasure_add_ofFun hx continuousOn_const, withDensity_const]

end GoodSample

end QuantumZipper
