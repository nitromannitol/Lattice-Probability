/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W5Fin2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W5Fin1

/-!
# W5 (part 10): de-integration in time (W5(ii), abstract form)

Node W5(ii) of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1): if two random (lifetime, path) pairs
`(L₁, p₁)`, `(L₂, p₂)` with continuous paths and integrable lifetimes have equal time-integrated
killed finite-dimensional functionals

`E ∫_{s>r} g(pₖ(s+uᵢ)) 1{s + U < Lₖ} ds`   (all `r ≥ 0`)

for a bounded continuous `g ≥ 0`, then already `E[g(p₁(uᵢ)); U < L₁] = E[g(p₂(uᵢ)); U < L₂]`
(`killed_fd_eq_of_integrated`). Proof, as in the blueprint: `s ↦ E[g(p(s+uᵢ)); s + U < L]` is
right-continuous (dominated convergence), and two right-continuous integrable functions with equal
integrals over all `(r, ∞)` agree (fundamental theorem of calculus, `eq_of_lintegral_Ioi_eq`).
Own elementary arguments.
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

/-- **De-integration.** Two measurable `K₁, K₂ ≥ 0` with finite, equal integrals over every
`(x, ∞)`, `x ≥ t`, whose real parts are right-continuous at `t`, agree at `t`. Own elementary
proof (FTC, `intervalIntegral.integral_hasDerivWithinAt_right`). -/
theorem eq_of_lintegral_Ioi_eq {K₁ K₂ : ℝ → ℝ≥0∞} (h1m : Measurable K₁) (h2m : Measurable K₂)
    {t : ℝ} (hfin1 : ∫⁻ s in Ioi t, K₁ s ≠ ∞) (hfin2 : ∫⁻ s in Ioi t, K₂ s ≠ ∞)
    (heq : ∀ x, t ≤ x → ∫⁻ s in Ioi x, K₁ s = ∫⁻ s in Ioi x, K₂ s)
    (hc1 : ContinuousWithinAt (fun s => (K₁ s).toReal) (Ioi t) t)
    (hc2 : ContinuousWithinAt (fun s => (K₂ s).toReal) (Ioi t) t) :
    (K₁ t).toReal = (K₂ t).toReal := by
  have hIoc : ∀ K : ℝ → ℝ≥0∞, Measurable K → ∫⁻ s in Ioi t, K s ≠ ∞ → ∀ x, t < x →
      ∫ y in t..x, (K y).toReal = (∫⁻ s in Ioc t x, K s).toReal := by
    intro K hK hfin x hx
    have hfin' : ∫⁻ s in Ioc t x, K s ≠ ∞ :=
      ne_top_of_le_ne_top hfin (lintegral_mono_set Ioc_subset_Ioi_self)
    rw [intervalIntegral.integral_of_le hx.le,
      integral_toReal hK.aemeasurable (ae_lt_top hK hfin')]
  have hsplit : ∀ K : ℝ → ℝ≥0∞, ∀ x, t ≤ x →
      ∫⁻ s in Ioi t, K s = (∫⁻ s in Ioc t x, K s) + ∫⁻ s in Ioi x, K s := by
    intro K x hx
    conv_lhs => rw [← Ioc_union_Ioi_eq_Ioi hx]
    exact lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same
  have hI : ∀ x, t < x → ∫ y in t..x, (K₁ y).toReal = ∫ y in t..x, (K₂ y).toReal := by
    intro x hx
    rw [hIoc K₁ h1m hfin1 x hx, hIoc K₂ h2m hfin2 x hx]
    congr 1
    have e1 := hsplit K₁ x hx.le
    have e2 := hsplit K₂ x hx.le
    rw [heq t le_rfl, e2, heq x hx.le] at e1
    have hx2 : ∫⁻ s in Ioi x, K₂ s ≠ ∞ :=
      ne_top_of_le_ne_top hfin2 (lintegral_mono_set (Ioi_subset_Ioi hx.le))
    exact ((ENNReal.add_left_inj hx2).1 e1).symm
  have hd1 := intervalIntegral.integral_hasDerivWithinAt_right (s := Ici t) (t := Ioi t)
    IntervalIntegrable.refl (h1m.ennreal_toReal.stronglyMeasurable.stronglyMeasurableAtFilter) hc1
  have hd2 := intervalIntegral.integral_hasDerivWithinAt_right (s := Ici t) (t := Ioi t)
    IntervalIntegrable.refl (h2m.ennreal_toReal.stronglyMeasurable.stronglyMeasurableAtFilter) hc2
  have hD := hd1.sub hd2
  have hD0 : HasDerivWithinAt ((fun u => ∫ x in t..u, (K₁ x).toReal)
      - fun u => ∫ x in t..u, (K₂ x).toReal) 0 (Ici t) t := by
    refine (hasDerivWithinAt_const (x := t) (s := Ici t) (c := (0 : ℝ))).congr_of_mem
      (fun x hx => ?_) (show t ∈ Ici t from mem_Ici.2 le_rfl)
    simp only [Pi.sub_apply]
    rcases eq_or_lt_of_le (show t ≤ x from hx) with h | h
    · subst h
      simp
    · rw [hI x h, sub_self]
  have := (uniqueDiffWithinAt_Ici t).eq_deriv _ hD hD0
  linarith

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The killed finite-dimensional functional at time shift `s`. -/
def killedFD (P : Measure Ω) (L : Ω → ℝ≥0) (p : Ω → ℝ≥0 → ℝ) {n : ℕ} (u : Fin n → ℝ≥0)
    (U : ℝ≥0) (g : (Fin n → ℝ) → ℝ≥0) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, {ω | s.toNNReal + U < L ω}.indicator
    (fun ω => (g (fun i => p ω (s.toNNReal + u i)) : ℝ≥0∞)) ω ∂P

theorem measurable_killedFD_integrand {L : Ω → ℝ≥0} {p : Ω → ℝ≥0 → ℝ} (hLm : Measurable L)
    (hpc : ∀ ω, Continuous (p ω)) (hpm : ∀ v, Measurable fun ω => p ω v) {n : ℕ}
    (u : Fin n → ℝ≥0) (U : ℝ≥0) {g : (Fin n → ℝ) → ℝ≥0} (hg : Continuous g) :
    Measurable fun q : Ω × ℝ => {q : Ω × ℝ | q.2.toNNReal + U < L q.1}.indicator
      (fun q => (g (fun i => p q.1 (q.2.toNNReal + u i)) : ℝ≥0∞)) q := by
  have hi : ∀ i, Measurable fun q : Ω × ℝ => p q.1 (q.2.toNNReal + u i) := fun i =>
    (measurable_uncurry_of_continuous_of_measurable
      (u := fun (s : ℝ) (ω : Ω) => p ω (s.toNNReal + u i))
      (fun ω => (hpc ω).comp (continuous_real_toNNReal.add continuous_const))
      (fun s => hpm _)).comp measurable_swap
  exact (measurable_coe_nnreal_ennreal.comp (hg.measurable.comp
    (measurable_pi_iff.2 hi))).indicator
    (measurableSet_lt (measurable_snd.real_toNNReal.add_const _) (hLm.comp measurable_fst))

/-- Right-continuity of the killed finite-dimensional functional (dominated convergence). -/
theorem continuousWithinAt_killedFD [IsFiniteMeasure P] {L : Ω → ℝ≥0} {p : Ω → ℝ≥0 → ℝ}
    (hLm : Measurable L) (hpc : ∀ ω, Continuous (p ω)) (hpm : ∀ v, Measurable fun ω => p ω v)
    {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) {g : (Fin n → ℝ) → ℝ≥0} (hg : Continuous g)
    {M : ℝ≥0} (hM : ∀ x, g x ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousWithinAt (fun s => (killedFD P L p u U g s).toReal) (Ioi t) t := by
  have hjm := measurable_killedFD_integrand hLm hpc hpm u U hg
  have hMfin : ∫⁻ _, (M : ℝ≥0∞) ∂P ≠ ∞ := by
    rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top P univ)
  have hfin : ∀ s, killedFD P L p u U g s ≠ ∞ := by
    intro s
    refine ne_top_of_le_ne_top hMfin ?_
    refine lintegral_mono fun ω => ?_
    by_cases h : ω ∈ {ω | s.toNNReal + U < L ω}
    · rw [indicator_of_mem h]; exact ENNReal.coe_le_coe.2 (hM _)
    · rw [indicator_of_notMem h]; exact zero_le
  refine (ENNReal.tendsto_toReal (hfin t)).comp ?_
  set S : ℝ → Set Ω := fun s => {ω | s.toNNReal + U < L ω} with hS
  set G : ℝ → Ω → ℝ≥0∞ := fun s ω => (g (fun i => p ω (s.toNNReal + u i)) : ℝ≥0∞) with hG
  show Tendsto (fun s => ∫⁻ ω, (S s).indicator (G s) ω ∂P) (𝓝[>] t)
    (𝓝 (∫⁻ ω, (S t).indicator (G t) ω ∂P))
  have hmeas : ∀ s, Measurable fun ω => (S s).indicator (G s) ω :=
    fun s => hjm.comp measurable_prodMk_right
  have hbd : ∀ s ω, (S s).indicator (G s) ω ≤ M := by
    intro s ω
    by_cases h : ω ∈ S s
    · rw [indicator_of_mem h]; exact ENNReal.coe_le_coe.2 (hM _)
    · rw [indicator_of_notMem h]; exact zero_le
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => (M : ℝ≥0∞))
    (Eventually.of_forall hmeas) (Eventually.of_forall fun s => Eventually.of_forall (hbd s))
    hMfin (Eventually.of_forall fun ω => ?_)
  have hcont : Continuous fun s : ℝ => G s ω :=
    ENNReal.continuous_coe.comp (hg.comp (continuous_pi fun i =>
      (hpc ω).comp (continuous_real_toNNReal.add continuous_const)))
  by_cases h : t.toNNReal + U < L ω
  · have hev : ∀ᶠ s in 𝓝[>] t, s.toNNReal + U < L ω :=
      nhdsWithin_le_nhds ((continuous_real_toNNReal.add continuous_const).continuousAt.eventually
        (isOpen_Iio.mem_nhds (show t.toNNReal + U ∈ Iio (L ω) from h)))
    rw [indicator_of_mem (show ω ∈ S t from h)]
    refine ((hcont.tendsto t).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hev] with s hs
    rw [indicator_of_mem (show ω ∈ S s from hs)]
  · refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hts : t.toNNReal < s.toNNReal :=
      (Real.toNNReal_lt_toNNReal_iff (ht.trans_lt hs)).2 hs
    rw [indicator_of_notMem (show ω ∉ S s from fun h' => h ((add_lt_add_of_lt_of_le hts le_rfl).trans h')),
      indicator_of_notMem (show ω ∉ S t from h)]

end QuantumZipper.Williams
