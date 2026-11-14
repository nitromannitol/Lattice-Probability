import LatticeProb.Analysis.HeatMollify

/-!
# Compactness of nonnegative classical solutions of the heat equation

For the operator `L = (2d)⁻¹ Δ` of `LatticeProb.WhiteNoise.contOp` on `ℝ × ℝ ^ d` and an open set
`U`, a sequence of nonnegative classical solutions of `∂_s u = L u` in `U` whose integrals over
every compact subset of `U` are bounded has a subsequence converging uniformly on the compact
subsets of `U` to a nonnegative classical solution.

The theorem `heatCompactness_of_interiorBounds` takes two analytic inputs as hypotheses: the
interior bounds of a classical solution and of its derivative by its local `L¹` norm, and the
regularity of continuous weak solutions. The interior bounds give local uniform bounds and, through
the mean value inequality, local equicontinuity; the Arzela-Ascoli theorem in `C(U, ℝ)`, which is
metrizable, gives a subsequence converging uniformly on compact sets. Classical solutions are weak
solutions by integration by parts, the weak equation passes to the uniform limit, and the regularity
of weak solutions applied to a cut-off of the limit shows that the limit is a classical solution
near every point of `U`.
-/

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Convolution
open LatticeProb.WhiteNoise

namespace LatticeProb.Heat

section Slices

variable {d : ℕ}

/-- The operator `contOp` at `x` only depends on the germ of the function at `x`. -/
theorem contOp_congr_of_eventuallyEq {φ φ' : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (h : φ =ᶠ[𝓝 x] φ') : contOp d φ x = contOp d φ' x := by
  unfold contOp lap
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : Continuous fun t : ℝ => Function.update x i t :=
    continuous_const.update i continuous_id
  have h2 : ∀ᶠ s in 𝓝 (x i), (fun t => φ (Function.update x i t)) =ᶠ[𝓝 s]
      fun t => φ' (Function.update x i t) := by
    filter_upwards [(hc.tendsto' (x i) x (by simp)).eventually h.eventually_nhds] with s hs
    exact (hc.tendsto s).eventually hs
  exact Filter.EventuallyEq.deriv_eq (h2.mono fun s hs => hs.deriv_eq)

/-- The time slice through `p` tends to `p`. -/
theorem tendsto_slice_fst (p : ℝ × (Fin d → ℝ)) :
    Tendsto (fun s : ℝ => (s, p.2)) (𝓝 p.1) (𝓝 p) :=
  (continuous_id.prodMk continuous_const).tendsto' p.1 p rfl

/-- The space slice through `p` tends to `p`. -/
theorem tendsto_slice_snd (p : ℝ × (Fin d → ℝ)) :
    Tendsto (fun x : Fin d → ℝ => (p.1, x)) (𝓝 p.2) (𝓝 p) :=
  (continuous_const.prodMk continuous_id).tendsto' p.2 p rfl

/-- The time derivative of a function vanishes off its topological support. -/
theorem deriv_slice_fst_eq_zero_of_notMem_tsupport {ψ : ℝ × (Fin d → ℝ) → ℝ} {p : ℝ × (Fin d → ℝ)}
    (hp : p ∉ tsupport ψ) : deriv (fun s => ψ (s, p.2)) p.1 = 0 := by
  have h : (fun s => ψ (s, p.2)) =ᶠ[𝓝 p.1] fun _ => 0 :=
    (tendsto_slice_fst p).eventually (notMem_tsupport_iff_eventuallyEq.1 hp)
  rw [h.deriv_eq, deriv_const]

/-- `contOp` of a space slice of a function vanishes off its topological support. -/
theorem contOp_slice_eq_zero_of_notMem_tsupport {ψ : ℝ × (Fin d → ℝ) → ℝ} {p : ℝ × (Fin d → ℝ)}
    (hp : p ∉ tsupport ψ) : contOp d (fun x => ψ (p.1, x)) p.2 = 0 := by
  have h : (fun x => ψ (p.1, x)) =ᶠ[𝓝 p.2] fun _ => 0 :=
    (tendsto_slice_snd p).eventually (notMem_tsupport_iff_eventuallyEq.1 hp)
  rw [contOp_congr_of_eventuallyEq h]
  simp [contOp, lap]

/-- The time derivative of a differentiable function as a directional derivative. -/
theorem hasDerivAt_slice_fst {w : ℝ × (Fin d → ℝ) → ℝ} {p : ℝ × (Fin d → ℝ)}
    (h : DifferentiableAt ℝ w p) :
    HasDerivAt (fun s => w (s, p.2)) (fderiv ℝ w p (1, 0)) p.1 :=
  h.hasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (s, p.2)) p.1
    ((hasDerivAt_id' p.1).prodMk (hasDerivAt_const p.1 p.2))

/-- The derivative in the `i`-th space coordinate as a directional derivative. -/
theorem hasDerivAt_slice_update {w : ℝ × (Fin d → ℝ) → ℝ} {a : ℝ} {x : Fin d → ℝ} {i : Fin d}
    {t : ℝ} (h : DifferentiableAt ℝ w (a, Function.update x i t)) :
    HasDerivAt (fun t => w (a, Function.update x i t))
      (fderiv ℝ w (a, Function.update x i t) (0, Pi.single i 1)) t :=
  h.hasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => (a, Function.update x i t)) t
    ((hasDerivAt_const t a).prodMk (hasDerivAt_update x i t))

/-- The `i`-th second partial derivative in space of the time slice, as an iterated directional
derivative. -/
theorem deriv_deriv_slice_update {w : ℝ × (Fin d → ℝ) → ℝ} {V : Set (ℝ × (Fin d → ℝ))}
    (hV : IsOpen V) (hw : ContDiffOn ℝ ∞ w V) {p : ℝ × (Fin d → ℝ)} (hp : p ∈ V) (i : Fin d) :
    deriv (fun s => deriv (fun t => w (p.1, Function.update p.2 i t)) s) (p.2 i) =
      fderiv ℝ (fun q => fderiv ℝ w q (0, Pi.single i 1)) p (0, Pi.single i 1) := by
  have hc : Continuous fun t : ℝ => ((p.1, Function.update p.2 i t) : ℝ × (Fin d → ℝ)) :=
    continuous_const.prodMk (continuous_const.update i continuous_id)
  have hp' : ((p.1, Function.update p.2 i (p.2 i)) : ℝ × (Fin d → ℝ)) = p := by simp
  have hev : ∀ᶠ s in 𝓝 (p.2 i), ((p.1, Function.update p.2 i s) : ℝ × (Fin d → ℝ)) ∈ V :=
    (hc.tendsto' (p.2 i) p hp').eventually (hV.mem_nhds hp)
  have hD : ContDiffOn ℝ ∞ (fun q => fderiv ℝ w q (0, Pi.single i 1)) V :=
    (hw.fderiv_of_isOpen hV (m := ∞) (by simp)).clm_apply contDiffOn_const
  have heq : (fun s => deriv (fun t => w (p.1, Function.update p.2 i t)) s) =ᶠ[𝓝 (p.2 i)]
      fun s => fderiv ℝ w (p.1, Function.update p.2 i s) (0, Pi.single i 1) := by
    filter_upwards [hev] with s hs
    exact (hasDerivAt_slice_update
      ((hw.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hs))).deriv
  rw [heq.deriv_eq]
  have hDp : DifferentiableAt ℝ (fun q => fderiv ℝ w q (0, Pi.single i 1))
      (p.1, Function.update p.2 i (p.2 i)) := by
    rw [hp']
    exact (hD.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp)
  rw [(hasDerivAt_slice_update hDp).deriv, hp']

/-- `contOp` of a time slice of a smooth function as a sum of iterated directional derivatives. -/
theorem contOp_slice_eq_sum {w : ℝ × (Fin d → ℝ) → ℝ} {V : Set (ℝ × (Fin d → ℝ))}
    (hV : IsOpen V) (hw : ContDiffOn ℝ ∞ w V) {p : ℝ × (Fin d → ℝ)} (hp : p ∈ V) :
    contOp d (fun x => w (p.1, x)) p.2 =
      (∑ i : Fin d, fderiv ℝ (fun q => fderiv ℝ w q (0, Pi.single i 1)) p (0, Pi.single i 1)) /
        (2 * d) := by
  unfold contOp lap
  congr 1
  exact Finset.sum_congr rfl fun i _ => deriv_deriv_slice_update hV hw hp i

end Slices

section Products

/-- The product of a function continuous on an open set `U` with a continuous function whose
topological support lies in `U` is continuous. -/
theorem continuous_mul_of_continuousOn_of_tsupport_subset {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsOpen U) {a b : X → ℝ} (ha : ContinuousOn a U) (hb : Continuous b)
    (hbU : tsupport b ⊆ U) : Continuous fun x => a x * b x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · exact (ha.continuousAt (hU.mem_nhds hx)).mul hb.continuousAt
  · refine (continuousAt_const : ContinuousAt (fun _ : X => (0 : ℝ)) x).congr ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hbU h)] with y hy
    simp only [Pi.zero_apply] at hy
    simp [hy]

variable {d : ℕ}

/-- The product of a function continuous on an open set `U` with a continuous compactly supported
function whose topological support lies in `U` is integrable. -/
theorem integrable_mul_of_continuousOn_of_tsupport_subset {U : Set (ℝ × (Fin d → ℝ))}
    (hU : IsOpen U) {a b : ℝ × (Fin d → ℝ) → ℝ} (ha : ContinuousOn a U) (hb : Continuous b)
    (hbc : HasCompactSupport b) (hbU : tsupport b ⊆ U) : Integrable fun p => a p * b p :=
  (continuous_mul_of_continuousOn_of_tsupport_subset hU ha hb hbU).integrable_of_hasCompactSupport
    (hbc.mul_left (f := a))

end Products

section Weak

variable {d : ℕ}

/-- A classical solution of the heat equation in an open set is a weak solution there. -/
theorem IsClassicalHeat.isWeakHeat {U : Set (ℝ × (Fin d → ℝ))} (hU : IsOpen U)
    {w : ℝ × (Fin d → ℝ) → ℝ} (hw : IsClassicalHeat d U w) : IsWeakHeat d U w := by
  intro ψ hψ hψc hψU
  obtain ⟨hwU, hwh⟩ := hw
  have hI : ∀ {a b : ℝ × (Fin d → ℝ) → ℝ}, ContinuousOn a U → Continuous b →
      HasCompactSupport b → tsupport b ⊆ U → Integrable fun p => a p * b p :=
    fun ha hb hbc hbU => integrable_mul_of_continuousOn_of_tsupport_subset hU ha hb hbc hbU
  have hwd : ∀ p ∈ U, DifferentiableAt ℝ w p := fun p hp =>
    (hwU.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hDw : ∀ v, ContDiffOn ℝ ∞ (fun q => fderiv ℝ w q v) U := fun v =>
    (hwU.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hDDw : ∀ v v', ContDiffOn ℝ ∞ (fun q => fderiv ℝ (fun q' => fderiv ℝ w q' v) q v') U :=
    fun v _ => ((hDw v).fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hDψ : ∀ v, ContDiff ℝ ∞ (fun q => fderiv ℝ ψ q v) := contDiff_fderiv_apply hψ
  have hDDψ : ∀ v v', ContDiff ℝ ∞ (fun q => fderiv ℝ (fun q' => fderiv ℝ ψ q' v) q v') :=
    fun v => contDiff_fderiv_apply (hDψ v)
  have hcDψ : ∀ v, HasCompactSupport (fun q => fderiv ℝ ψ q v) := fun v =>
    hψc.fderiv_apply (𝕜 := ℝ) v
  have hcDDψ : ∀ v v', HasCompactSupport (fun q => fderiv ℝ (fun q' => fderiv ℝ ψ q' v) q v') :=
    fun v v' => (hcDψ v).fderiv_apply (𝕜 := ℝ) v'
  have htDψ : ∀ v, tsupport (fun q => fderiv ℝ ψ q v) ⊆ U := fun v =>
    (tsupport_fderiv_apply_subset v).trans hψU
  have htDDψ : ∀ v v', tsupport (fun q => fderiv ℝ (fun q' => fderiv ℝ ψ q' v) q v') ⊆ U :=
    fun v v' => (tsupport_fderiv_apply_subset v').trans (htDψ v)
  have ibp0 : ∫ p, w p * fderiv ℝ ψ p (1, 0) = -∫ p, fderiv ℝ w p (1, 0) * ψ p :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (hI (hDw _).continuousOn hψ.continuous hψc hψU)
      (hI hwU.continuousOn (hDψ _).continuous (hcDψ _)
        (htDψ _))
      (hI hwU.continuousOn hψ.continuous hψc hψU)
      (fun p hp => hwd p (hψU hp)) (fun p _ => hψd p)
  have ibp : ∀ i : Fin d,
      ∫ p, w p * fderiv ℝ (fun q => fderiv ℝ ψ q (0, Pi.single i 1)) p (0, Pi.single i 1) =
        ∫ p, fderiv ℝ (fun q => fderiv ℝ w q (0, Pi.single i 1)) p (0, Pi.single i 1) * ψ p := by
    intro i
    calc ∫ p, w p * fderiv ℝ (fun q => fderiv ℝ ψ q (0, Pi.single i 1)) p (0, Pi.single i 1)
        = -∫ p, fderiv ℝ w p (0, Pi.single i 1) * fderiv ℝ ψ p (0, Pi.single i 1) :=
          integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
            (hI (hDw _).continuousOn (hDψ _).continuous
              (hcDψ _) (htDψ _))
            (hI hwU.continuousOn (hDDψ _ _).continuous
              (hcDDψ _ _) (htDDψ _ _))
            (hI hwU.continuousOn (hDψ _).continuous
              (hcDψ _) (htDψ _))
            (fun p hp => hwd p (htDψ _ hp)) (fun p _ => (hDψ _).differentiable (by simp) p)
      _ = -(-∫ p, fderiv ℝ (fun q => fderiv ℝ w q (0, Pi.single i 1)) p (0, Pi.single i 1) *
            ψ p) := by
          congr 1
          exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
            (hI (hDDw _ _).continuousOn hψ.continuous hψc hψU)
            (hI (hDw _).continuousOn (hDψ _).continuous
              (hcDψ _) (htDψ _))
            (hI (hDw _).continuousOn hψ.continuous hψc hψU)
            (fun p hp => ((hDw _).differentiableOn (by simp)).differentiableAt
              (hU.mem_nhds (hψU hp)))
            (fun p _ => hψd p)
      _ = _ := neg_neg _
  have hS : ∀ p, contOp d (fun x => ψ (p.1, x)) p.2 =
      (∑ i : Fin d, fderiv ℝ (fun q => fderiv ℝ ψ q (0, Pi.single i 1)) p (0, Pi.single i 1)) /
        (2 * d) := fun p =>
    contOp_slice_eq_sum isOpen_univ hψ.contDiffOn (mem_univ p)
  have hT : ∀ p : ℝ × (Fin d → ℝ), deriv (fun s => ψ (s, p.2)) p.1 = fderiv ℝ ψ p (1, 0) :=
    fun p => (hasDerivAt_slice_fst (hψd p)).deriv
  have hW : ∀ p, fderiv ℝ w p (1, 0) * ψ p =
      (∑ i : Fin d, fderiv ℝ (fun q => fderiv ℝ w q (0, Pi.single i 1)) p (0, Pi.single i 1)) /
        (2 * d) * ψ p := by
    intro p
    by_cases hp : p ∈ U
    · rw [(hasDerivAt_slice_fst (hwd p hp)).unique (hwh p hp), contOp_slice_eq_sum hU hwU hp]
    · rw [image_eq_zero_of_notMem_tsupport fun h => hp (hψU h), mul_zero, mul_zero]
  have hint : ∀ i : Fin d, Integrable fun p =>
      fderiv ℝ (fun q => fderiv ℝ w q (0, Pi.single i 1)) p (0, Pi.single i 1) * ψ p := fun i =>
    hI (hDDw _ _).continuousOn hψ.continuous hψc hψU
  have hint' : ∀ i : Fin d, Integrable fun p =>
      w p * fderiv ℝ (fun q => fderiv ℝ ψ q (0, Pi.single i 1)) p (0, Pi.single i 1) := fun i =>
    hI hwU.continuousOn (hDDψ _ _).continuous (hcDDψ _ _)
      (htDDψ _ _)
  calc -∫ p, w p * deriv (fun s => ψ (s, p.2)) p.1
      = -∫ p, w p * fderiv ℝ ψ p (1, 0) := by simp only [hT]
    _ = ∫ p, fderiv ℝ w p (1, 0) * ψ p := by rw [ibp0, neg_neg]
    _ = ∫ p, (∑ i : Fin d, fderiv ℝ (fun q => fderiv ℝ w q (0, Pi.single i 1)) p
          (0, Pi.single i 1) * ψ p) / (2 * d) := by
        congr 1
        funext p
        rw [hW p, div_mul_eq_mul_div, Finset.sum_mul]
    _ = (∑ i : Fin d, ∫ p, fderiv ℝ (fun q => fderiv ℝ w q (0, Pi.single i 1)) p
          (0, Pi.single i 1) * ψ p) / (2 * d) := by
        rw [integral_div, integral_finsetSum _ fun i _ => hint i]
    _ = (∑ i : Fin d, ∫ p, w p * fderiv ℝ (fun q => fderiv ℝ ψ q (0, Pi.single i 1)) p
          (0, Pi.single i 1)) / (2 * d) := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => (ibp i).symm
    _ = ∫ p, w p * contOp d (fun x => ψ (p.1, x)) p.2 := by
        rw [← integral_finsetSum _ fun i _ => hint' i, ← integral_div]
        congr 1
        funext p
        rw [hS p, ← mul_div_assoc, Finset.mul_sum]

/-- The weak equation only sees the function on the support of the test function. -/
theorem IsWeakHeat.mono_of_eqOn {U V : Set (ℝ × (Fin d → ℝ))} {u u' : ℝ × (Fin d → ℝ) → ℝ}
    (h : IsWeakHeat d U u) (hVU : V ⊆ U) (huu : EqOn u u' V) : IsWeakHeat d V u' := by
  intro ψ hψ hψc hψV
  have e0 : ∀ p : ℝ × (Fin d → ℝ), u' p * deriv (fun s => ψ (s, p.2)) p.1 =
      u p * deriv (fun s => ψ (s, p.2)) p.1 := by
    intro p
    by_cases hp : p ∈ tsupport ψ
    · rw [huu (hψV hp)]
    · rw [deriv_slice_fst_eq_zero_of_notMem_tsupport hp, mul_zero, mul_zero]
  have e1 : ∀ p : ℝ × (Fin d → ℝ), u' p * contOp d (fun x => ψ (p.1, x)) p.2 =
      u p * contOp d (fun x => ψ (p.1, x)) p.2 := by
    intro p
    by_cases hp : p ∈ tsupport ψ
    · rw [huu (hψV hp)]
    · rw [contOp_slice_eq_zero_of_notMem_tsupport hp, mul_zero, mul_zero]
  simp only [e0, e1]
  exact h ψ hψ hψc (hψV.trans hVU)

/-- The integral of `F n * Φ` converges to that of `v * Φ` when `F n → v` uniformly on a compact
set containing the support of the continuous function `Φ`. -/
theorem tendsto_integral_mul_of_tendstoUniformlyOn_support {U K : Set (ℝ × (Fin d → ℝ))}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {F : ℕ → ℝ × (Fin d → ℝ) → ℝ}
    {v : ℝ × (Fin d → ℝ) → ℝ} (hFc : ∀ n, ContinuousOn (F n) U) (hvc : ContinuousOn v U)
    (hlim : TendstoUniformlyOn F v atTop K) {Φ : ℝ × (Fin d → ℝ) → ℝ} (hΦ : Continuous Φ)
    (hΦK : Function.support Φ ⊆ K) :
    Tendsto (fun n => ∫ p, F n p * Φ p) atTop (𝓝 (∫ p, v p * Φ p)) := by
  have hKc : IsClosed K := hK.isClosed
  have hΦc : HasCompactSupport Φ :=
    HasCompactSupport.intro hK fun p hp => Function.notMem_support.1 fun h => hp (hΦK h)
  have hΦU : tsupport Φ ⊆ U := (closure_minimal hΦK hKc).trans hKU
  have hiF : ∀ n, Integrable fun p => F n p * Φ p := fun n =>
    integrable_mul_of_continuousOn_of_tsupport_subset hU (hFc n) hΦ hΦc hΦU
  have hiv : Integrable fun p => v p * Φ p :=
    integrable_mul_of_continuousOn_of_tsupport_subset hU hvc hΦ hΦc hΦU
  have hiΦ : Integrable fun p => |Φ p| := (hΦ.integrable_of_hasCompactSupport hΦc).abs
  set I := ∫ p, |Φ p|
  have hI : 0 ≤ I := integral_nonneg fun _ => abs_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hη : 0 < ε / (I + 1) := div_pos hε (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hlim _ hη)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm, ← integral_sub (hiF n) hiv]
  have hb : ∀ p, ‖F n p * Φ p - v p * Φ p‖ ≤ ε / (I + 1) * |Φ p| := by
    intro p
    rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hp : p ∈ K
    · have := hN n hn p hp
      rw [dist_comm, Real.dist_eq] at this
      exact mul_le_mul_of_nonneg_right this.le (abs_nonneg _)
    · have : Φ p = 0 := Function.notMem_support.1 fun h => hp (hΦK h)
      simp [this]
  calc ‖∫ p, (F n p * Φ p - v p * Φ p)‖
      ≤ ∫ p, ε / (I + 1) * |Φ p| :=
        norm_integral_le_of_norm_le (hiΦ.const_mul _) (Eventually.of_forall hb)
    _ = ε / (I + 1) * I := integral_const_mul _ _
    _ < ε / (I + 1) * (I + 1) := mul_lt_mul_of_pos_left (lt_add_one I) hη
    _ = ε := div_mul_cancel₀ ε (by linarith)

/-- The weak equation passes to limits uniform on compact sets. -/
theorem IsWeakHeat.of_tendstoUniformlyOn {U : Set (ℝ × (Fin d → ℝ))} (hU : IsOpen U)
    {F : ℕ → ℝ × (Fin d → ℝ) → ℝ} {v : ℝ × (Fin d → ℝ) → ℝ} (hF : ∀ n, IsWeakHeat d U (F n))
    (hFc : ∀ n, ContinuousOn (F n) U) (hvc : ContinuousOn v U)
    (hlim : ∀ K, IsCompact K → K ⊆ U → TendstoUniformlyOn F v atTop K) : IsWeakHeat d U v := by
  intro ψ hψ hψc hψU
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hT : (fun p : ℝ × (Fin d → ℝ) => deriv (fun s => ψ (s, p.2)) p.1) =
      fun p => fderiv ℝ ψ p (1, 0) := funext fun p => (hasDerivAt_slice_fst (hψd p)).deriv
  have hS : (fun p : ℝ × (Fin d → ℝ) => contOp d (fun x => ψ (p.1, x)) p.2) =
      fun p => (∑ i : Fin d,
        fderiv ℝ (fun q => fderiv ℝ ψ q (0, Pi.single i 1)) p (0, Pi.single i 1)) / (2 * d) :=
    funext fun p => contOp_slice_eq_sum isOpen_univ hψ.contDiffOn (mem_univ p)
  have hΦ0 : Continuous fun p : ℝ × (Fin d → ℝ) => deriv (fun s => ψ (s, p.2)) p.1 := by
    rw [hT]; exact (contDiff_fderiv_apply hψ _).continuous
  have hΦ1 : Continuous fun p : ℝ × (Fin d → ℝ) => contOp d (fun x => ψ (p.1, x)) p.2 := by
    rw [hS]
    exact (continuous_finsetSum _ fun i _ =>
      (contDiff_fderiv_apply (contDiff_fderiv_apply hψ _) _).continuous).div_const _
  have hs0 : Function.support (fun p : ℝ × (Fin d → ℝ) => deriv (fun s => ψ (s, p.2)) p.1) ⊆
      tsupport ψ := fun p hp => by
    by_contra h
    exact hp (deriv_slice_fst_eq_zero_of_notMem_tsupport h)
  have hs1 : Function.support (fun p : ℝ × (Fin d → ℝ) => contOp d (fun x => ψ (p.1, x)) p.2) ⊆
      tsupport ψ := fun p hp => by
    by_contra h
    exact hp (contOp_slice_eq_zero_of_notMem_tsupport h)
  have hlhs := (tendsto_integral_mul_of_tendstoUniformlyOn_support hU hψc hψU hFc hvc
    (hlim _ hψc hψU) hΦ0 hs0).neg
  have hrhs := tendsto_integral_mul_of_tendstoUniformlyOn_support hU hψc hψU hFc hvc
    (hlim _ hψc hψU) hΦ1 hs1
  have heq : (fun n => -∫ p, F n p * deriv (fun s => ψ (s, p.2)) p.1) =
      fun n => ∫ p, F n p * contOp d (fun x => ψ (p.1, x)) p.2 :=
    funext fun n => hF n ψ hψ hψc hψU
  rw [heq] at hlhs
  exact tendsto_nhds_unique hlhs hrhs

end Weak

section Ascoli

/-- **Arzela-Ascoli** on an open subset of a proper metric space: a sequence of functions continuous
on `U`, pointwise bounded and equicontinuous at every point of `U`, has a subsequence converging
uniformly on every compact subset of `U` to a function continuous on `U`. -/
theorem exists_strictMono_tendstoUniformlyOn {X : Type*} [MetricSpace X] [ProperSpace X]
    {U : Set X} (hU : IsOpen U) {f : ℕ → X → ℝ} (hfc : ∀ n, ContinuousOn (f n) U)
    (hbd : ∀ x ∈ U, ∃ M, ∀ n, |f n x| ≤ M)
    (heq : ∀ x ∈ U, ∀ ε > 0, ∀ᶠ y in 𝓝 x, ∀ n, dist (f n x) (f n y) < ε) :
    ∃ (r : ℕ → ℕ) (v : X → ℝ), StrictMono r ∧ ContinuousOn v U ∧
      ∀ K, IsCompact K → K ⊆ U → TendstoUniformlyOn (fun n => f (r n)) v atTop K := by
  classical
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  let g : ℕ → C(U, ℝ) := fun n =>
    ⟨U.domRestrict (f n), continuousOn_iff_continuous_domRestrict.1 (hfc n)⟩
  have hemb : IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set U | IsCompact K} ∘ ((↑) : C(U, ℝ) → U → ℝ)) := by
    refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
    change IsClosed (range ContinuousMap.toUniformOnFunIsCompact)
    rw [ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith
  have heqc : ∀ K ∈ {K : Set U | IsCompact K},
      EquicontinuousOn (((↑) : C(U, ℝ) → U → ℝ) ∘ ((↑) : range g → C(U, ℝ))) K := by
    intro K _
    refine Equicontinuous.equicontinuousOn (fun x₀ => ?_) K
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    filter_upwards [(continuous_subtype_val.tendsto x₀).eventually (heq x₀ x₀.2 ε hε)] with y hy
    rintro ⟨_, n, rfl⟩
    exact hy n
  have hpw : ∀ K ∈ {K : Set U | IsCompact K}, ∀ x ∈ K,
      ∃ Q, IsCompact Q ∧ ∀ i ∈ range g, (i : U → ℝ) x ∈ Q := by
    intro K _ x _
    obtain ⟨M, hM⟩ := hbd x x.2
    refine ⟨closedBall 0 M, isCompact_closedBall 0 M, ?_⟩
    rintro _ ⟨n, rfl⟩
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs]
    exact hM n
  have hcpt : IsCompact (closure (range g)) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun K hK => hK) hemb heqc hpw
  obtain ⟨G, -, r, hr, hG⟩ := hcpt.tendsto_subseq fun n => subset_closure (mem_range_self n)
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn] at hG
  refine ⟨r, fun x => if h : x ∈ U then G ⟨x, h⟩ else 0, hr, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert G.continuous using 1
    funext x
    simp [Set.domRestrict]
  · intro K hK hKU
    have hK' : IsCompact (((↑) : U → X) ⁻¹' K) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hKU]
      exact hK
    have h := hG _ hK'
    rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    intro ε hε
    filter_upwards [h ε hε] with n hn x hx
    have := hn ⟨x, hKU hx⟩ hx
    convert this using 2 <;> first | rfl | simp [hKU hx]

end Ascoli

/-- **Compactness of nonnegative classical solutions of the heat equation**, with the interior
bounds of classical solutions (`hIB`) and the regularity of continuous weak solutions (`hWR`) as
hypotheses: a sequence of nonnegative classical solutions in an open set `U` with bounded integrals
over the compact subsets of `U` has a subsequence converging uniformly on the compact subsets of `U`
to a nonnegative classical solution. -/
theorem heatCompactness_of_interiorBounds
    (hIB : ∀ (d : ℕ), 1 ≤ d → ∀ (O : Set (ℝ × (Fin d → ℝ))), IsOpen O → ∀ K : Set (ℝ × (Fin d → ℝ)),
      IsCompact K → K ⊆ O → ∃ (K' : Set (ℝ × (Fin d → ℝ))) (C : ℝ), IsCompact K' ∧ K' ⊆ O ∧
        ∀ w : ℝ × (Fin d → ℝ) → ℝ, IsClassicalHeat d O w → ∀ p ∈ K,
          |w p| ≤ C * ∫ q in K', |w q| ∧ ‖fderiv ℝ w p‖ ≤ C * ∫ q in K', |w q|)
    (hWR : ∀ (d : ℕ) (U : Set (ℝ × (Fin d → ℝ))), IsOpen U → ∀ u : ℝ × (Fin d → ℝ) → ℝ,
      Continuous u →
      IsWeakHeat d U u → ∃ v : ℝ × (Fin d → ℝ) → ℝ, IsClassicalHeat d U v ∧ ∀ p ∈ U, u p = v p) :
    ∀ (d : ℕ), 1 ≤ d → ∀ (U : Set (ℝ × (Fin d → ℝ))), IsOpen U →
      ∀ f : ℕ → ℝ × (Fin d → ℝ) → ℝ,
        (∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (f n) U) →
        (∀ n p, p ∈ U → 0 ≤ f n p) →
        (∀ n p, p ∈ U → HasDerivAt (fun s => f n (s, p.2))
          (contOp d (fun x => f n (p.1, x)) p.2) p.1) →
        (∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → K ⊆ U →
          ∃ C : ℝ, ∀ n, IntegrableOn (f n) K ∧ (∫ p in K, ‖f n p‖) ≤ C) →
        ∃ (r : ℕ → ℕ) (v : ℝ × (Fin d → ℝ) → ℝ), StrictMono r ∧
          ContDiffOn ℝ (⊤ : ℕ∞) v U ∧
          (∀ p ∈ U, 0 ≤ v p) ∧
          (∀ p ∈ U, HasDerivAt (fun s => v (s, p.2))
            (contOp d (fun x => v (p.1, x)) p.2) p.1) ∧
          (∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → K ⊆ U →
            TendstoUniformlyOn (fun n => f (r n)) v atTop K) := by
  intro d hd U hU f hf1 hf0 hf3 hf4
  have hcl : ∀ n, IsClassicalHeat d U (f n) := fun n => ⟨hf1 n, hf3 n⟩
  have hloc : ∀ p ∈ U, ∃ ρ > 0, closedBall p ρ ⊆ U ∧ ∃ M, ∀ n, ∀ q ∈ closedBall p ρ,
      |f n q| ≤ M ∧ ‖fderiv ℝ (f n) q‖ ≤ M := by
    intro p hp
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU p hp
    have hsub : closedBall p (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hball
    refine ⟨ε / 2, half_pos hε, hsub, ?_⟩
    obtain ⟨K', C, hK'c, hK'U, hb⟩ := hIB d hd U hU _ (isCompact_closedBall p _) hsub
    obtain ⟨C', hC'⟩ := hf4 K' hK'c hK'U
    refine ⟨|C| * C', fun n q hq => ?_⟩
    have hI : ∫ q in K', |f n q| ≤ C' := by simpa [Real.norm_eq_abs] using (hC' n).2
    have hI0 : 0 ≤ ∫ q in K', |f n q| := integral_nonneg fun _ => abs_nonneg _
    have hCI : C * ∫ q in K', |f n q| ≤ |C| * C' :=
      (mul_le_mul_of_nonneg_right (le_abs_self C) hI0).trans
        (mul_le_mul_of_nonneg_left hI (abs_nonneg C))
    obtain ⟨h1, h2⟩ := hb (f n) (hcl n) q hq
    exact ⟨h1.trans hCI, h2.trans hCI⟩
  have hbd : ∀ p ∈ U, ∃ M, ∀ n, |f n p| ≤ M := by
    intro p hp
    obtain ⟨ρ, hρ, -, M, hM⟩ := hloc p hp
    exact ⟨M, fun n => (hM n p (mem_closedBall_self hρ.le)).1⟩
  have heq : ∀ p ∈ U, ∀ ε > 0, ∀ᶠ q in 𝓝 p, ∀ n, dist (f n p) (f n q) < ε := by
    intro p hp ε hε
    obtain ⟨ρ, hρ, hρU, M, hM⟩ := hloc p hp
    have hδ : 0 < ε / (|M| + 1) := div_pos hε (by positivity)
    filter_upwards [ball_mem_nhds p hρ, ball_mem_nhds p hδ] with q hq hqδ n
    have hqc : q ∈ closedBall p ρ := ball_subset_closedBall hq
    have hmv := (convex_closedBall p ρ).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => ((hf1 n).differentiableOn (by simp)).differentiableAt
        (hU.mem_nhds (hρU hz)))
      (fun z hz => (hM n z hz).2) (mem_closedBall_self hρ.le) hqc
    rw [mem_ball, dist_eq_norm] at hqδ
    rw [dist_comm, dist_eq_norm]
    calc ‖f n q - f n p‖ ≤ M * ‖q - p‖ := hmv
      _ ≤ (|M| + 1) * ‖q - p‖ :=
        mul_le_mul_of_nonneg_right ((le_abs_self M).trans (le_add_of_nonneg_right zero_le_one))
          (norm_nonneg _)
      _ < (|M| + 1) * (ε / (|M| + 1)) := mul_lt_mul_of_pos_left hqδ (by positivity)
      _ = ε := mul_div_cancel₀ ε (by positivity)
  obtain ⟨r, v, hr, hvc, hvlim⟩ := exists_strictMono_tendstoUniformlyOn hU
    (fun n => (hf1 n).continuousOn) hbd heq
  have hvw : IsWeakHeat d U v := IsWeakHeat.of_tendstoUniformlyOn hU
    (fun n => (hcl (r n)).isWeakHeat hU) (fun n => (hf1 (r n)).continuousOn) hvc hvlim
  have hreg : ∀ p ∈ U, ∃ ρ > 0, ∃ w : ℝ × (Fin d → ℝ) → ℝ, IsClassicalHeat d (ball p ρ) w ∧
      ∀ q ∈ ball p ρ, v q = w q := by
    intro p hp
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU p hp
    let χ : ContDiffBump p := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
    have hχU : tsupport χ ⊆ U := by
      rw [χ.tsupport_eq]
      exact (closedBall_subset_ball (by simp only [χ]; linarith)).trans hball
    have hu : Continuous fun q => v q * χ q :=
      continuous_mul_of_continuousOn_of_tsupport_subset hU hvc χ.continuous hχU
    have hBU : ball p (ε / 4) ⊆ U := (ball_subset_ball (by linarith)).trans hball
    have hwk : IsWeakHeat d (ball p (ε / 4)) fun q => v q * χ q :=
      hvw.mono_of_eqOn hBU fun q hq => by
        rw [χ.one_of_mem_closedBall (ball_subset_closedBall hq), mul_one]
    obtain ⟨w, hw, hwv⟩ := hWR d (ball p (ε / 4)) isOpen_ball _ hu hwk
    refine ⟨ε / 4, by positivity, w, hw, fun q hq => ?_⟩
    rw [← hwv q hq, χ.one_of_mem_closedBall (ball_subset_closedBall hq), mul_one]
  refine ⟨r, v, hr, ?_, ?_, ?_, hvlim⟩
  · intro p hp
    obtain ⟨ρ, hρ, w, hw, hvw'⟩ := hreg p hp
    have hev : v =ᶠ[𝓝 p] w := eventuallyEq_of_mem (ball_mem_nhds p hρ) hvw'
    exact ((hw.1.contDiffAt (ball_mem_nhds p hρ)).congr_of_eventuallyEq hev).contDiffWithinAt
  · intro p hp
    have h := (hvlim {p} isCompact_singleton (singleton_subset_iff.2 hp)).tendsto_at
      (mem_singleton p)
    exact ge_of_tendsto' h fun n => hf0 _ p hp
  · intro p hp
    obtain ⟨ρ, hρ, w, hw, hvw'⟩ := hreg p hp
    have hev : v =ᶠ[𝓝 p] w := eventuallyEq_of_mem (ball_mem_nhds p hρ) hvw'
    have h1 : (fun s => v (s, p.2)) =ᶠ[𝓝 p.1] fun s => w (s, p.2) :=
      (tendsto_slice_fst p).eventually hev
    have h2 : (fun x => v (p.1, x)) =ᶠ[𝓝 p.2] fun x => w (p.1, x) :=
      (tendsto_slice_snd p).eventually hev
    rw [contOp_congr_of_eventuallyEq h2]
    exact (hw.2 p (mem_ball_self hρ)).congr_of_eventuallyEq h1

end LatticeProb.Heat
