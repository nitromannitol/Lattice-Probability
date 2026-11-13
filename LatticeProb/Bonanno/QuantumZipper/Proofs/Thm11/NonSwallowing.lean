/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm11.NonSwallowing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm11.NonSwallowingLyap
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm11.ForwardClock
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.OptionalStopping
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Increments
import LatticeProb.Bonanno.QuantumZipper.SLE.Defs

/-!
# DF-2: non-swallowing of fixed points and zero area of the hull, `κ ∈ (0,4]`

Blueprint `THM11_BLUEPRINT.md` §1 (issue 2) and §5. For `a ∈ ℍ` we run the `c`-tamed
one-point motion `U_t = tamedZ (drive κ B ω) c a t`, which solves
`dU = tamedZField c U dt − √κ dB` (Lipschitz, bounded drift), apply the Dynkin formula
(`Dynkin.dynkin_additive`) to a smooth cutoff `F` of the Lyapunov function
`V = −log|z| + ((4−κ)/4) g(arg z) + ε|z|²`, and stop at the exit time `τ` of the annular region
`{ρ < |z| < R, Im z > c}` (capped at `T`). Where the taming is inactive `LV ≤ ε(κ+4)`, so
`E F(U_τ) ≤ F(a) + Tε(κ+4)`. On the event `a ∈ K_T` the motion must leave the annulus before
`T`, and (by the clock identity `Im f_t = Im a·e^{−2S_t}`) not through `Im z = c`; hence
`F(U_τ) ≥ −log ρ − C` or `F(U_τ) ≥ −log R + εR² − C`. Markov's inequality and
`ρ = e^{−R}`, `ε = 1/R`, `R → ∞` give `P(a ∈ K_T) = 0`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

noncomputable section

namespace QuantumZipper
namespace NonSwallow

open FwdClock Thm11Lyap FwdHolo

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ### The natural filtration and the tamed process -/

/-- The natural filtration of `B`, as a `Filtration`. -/
def bmFilt (hBm : ∀ r, Measurable (B r)) : Filtration ℝ≥0 mΩ where
  seq := bmFiltration B
  mono' := fun _ t hst => iSup₂_le fun r hr =>
    le_iSup₂_of_le (f := fun r (_ : r ≤ t) => (inferInstance : MeasurableSpace ℝ).comap (B r))
      r (hr.trans hst) le_rfl
  le' := bmFiltration_le hBm

theorem bmFilt_adapted (hBm : ∀ r, Measurable (B r)) (t : ℝ≥0) :
    Measurable[bmFilt hBm t] (B t) :=
  measurable_iff_comap_le.2
    (le_iSup₂_of_le (f := fun r (_ : r ≤ t) => (inferInstance : MeasurableSpace ℝ).comap (B r))
      t le_rfl le_rfl)

theorem bmFilt_le_past (hBm : ∀ r, Measurable (B r)) (t : ℝ≥0) :
    bmFilt hBm t ≤
      MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi :=
  bmFiltration_le_comap_restrict t

theorem continuous_drive_ns (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) (ω : Ω) :
    Continuous (drive κ B ω) :=
  continuous_const.mul ((hBc ω).comp continuous_real_toNNReal)

/-- The tamed one-point motion solves the additive-noise integral equation of `Dynkin`. -/
theorem tamedZ_integralEq (hBc : ∀ ω, Continuous fun t => B t ω) {c : ℝ} (hc : 0 < c)
    (κ : ℝ) (a : ℂ) (ω : Ω) (t : ℝ≥0) :
    tamedZ (drive κ B ω) c a t = a
      + (∫ r in (0 : ℝ)..t, tamedZField c (tamedZ (drive κ B ω) c a (r.toNNReal : ℝ)))
      + B t ω • (-((Real.sqrt κ : ℝ) : ℂ)) := by
  rw [tamedZ_eq (continuous_drive_ns hBc κ ω) hc a t.coe_nonneg]
  have hint : ∫ s in (0 : ℝ)..t, 2 / proj c (tamedZ (drive κ B ω) c a s)
      = ∫ r in (0 : ℝ)..t, tamedZField c (tamedZ (drive κ B ω) c a (r.toNNReal : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le t.coe_nonneg] at hr
    simp only [tamedZField, Real.coe_toNNReal r hr.1]
  rw [hint]
  simp only [drive, Real.toNNReal_coe, Complex.real_smul]
  push_cast
  ring

theorem lipschitz_tamedZField {c : ℝ} (hc : 0 < c) :
    LipschitzWith (Real.toNNReal (4 / c ^ 2)) (tamedZField c) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
  have h := norm_two_div_sub_le_tamed hc (norm_proj_ge_tamed c x) (norm_proj_ge_tamed c y)
  have hp : ‖proj c x - proj c y‖ ≤ 2 * ‖x - y‖ := by
    have := (proj_lipschitz c).dist_le_mul x y
    simpa [dist_eq_norm] using this
  calc ‖tamedZField c x - tamedZField c y‖ = ‖2 / proj c x - 2 / proj c y‖ := rfl
    _ ≤ 2 * ‖proj c x - proj c y‖ / c ^ 2 := h
    _ ≤ 2 * (2 * ‖x - y‖) / c ^ 2 := by gcongr
    _ = 4 / c ^ 2 * ‖x - y‖ := by ring

/-! ### Optional stopping for the Dynkin martingale -/

theorem martingale_min_const {M : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [IsFiniteMeasure P]
    (hM : Martingale M 𝓕 P) (T : ℝ≥0) : Martingale (fun t => M (min t T)) 𝓕 P := by
  refine ⟨fun t => (hM.stronglyAdapted (min t T)).mono (𝓕.mono (min_le_left _ _)),
    fun s t hst => ?_⟩
  by_cases hsT : s ≤ T
  · have := hM.2 s (min t T) (le_min hst hsT)
    show P[M (min t T) | 𝓕 s] =ᵐ[P] M (min s T)
    rw [min_eq_left hsT]; exact this
  · push Not at hsT
    show P[M (min t T) | 𝓕 s] =ᵐ[P] M (min s T)
    rw [min_eq_right (hsT.le.trans hst), min_eq_right hsT.le,
      condExp_of_stronglyMeasurable (𝓕.le s) ((hM.stronglyAdapted T).mono (𝓕.mono hsT.le))
        (hM.integrable T)]

theorem abs_dynkinGen_le {b : ℂ → ℂ} {e : ℂ} {F : ℂ → ℝ} {C Mb : ℝ} (hC : 0 ≤ C)
    (hbM : ∀ x, ‖b x‖ ≤ Mb)
    (hD : ∀ x, ‖fderiv ℝ F x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 F x‖ ≤ C ∧
      ‖iteratedFDeriv ℝ 3 F x‖ ≤ C) (x : ℂ) :
    |dynkinGen b e F x| ≤ C * Mb + 1 / 2 * (C * ‖e‖ ^ 2) := by
  unfold dynkinGen
  have h1 : |fderiv ℝ F x (b x)| ≤ C * Mb := by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ F x).le_opNorm (b x)).trans
      (mul_le_mul (hD x).1 (hbM x) (norm_nonneg _) hC)
  have h2 : |iteratedFDeriv ℝ 2 F x ![e, e]| ≤ C * ‖e‖ ^ 2 :=
    (Dynkin.abs_iteratedFDeriv_two_vec_le F x e).trans
      (mul_le_mul_of_nonneg_right (hD x).2.1 (by positivity))
  calc |fderiv ℝ F x (b x) + 1 / 2 * iteratedFDeriv ℝ 2 F x ![e, e]|
      ≤ |fderiv ℝ F x (b x)| + |1 / 2 * iteratedFDeriv ℝ 2 F x ![e, e]| := abs_add_le _ _
    _ ≤ C * Mb + 1 / 2 * (C * ‖e‖ ^ 2) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith

/-- **Stopped Dynkin identity.** For a bounded stopping time `τ ≤ T`,
`E[F(U_τ) − F(u) − ∫₀^τ LF(U_r) dr] = 0`, and the integrand is integrable. -/
theorem dynkin_stopped (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (𝓕 : Filtration ℝ≥0 mΩ) (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hpast : ∀ t, 𝓕 t ≤ MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi)
    {b : ℂ → ℂ} {Lb : ℝ≥0} {Mb : ℝ} (hb : LipschitzWith Lb b) (hbM : ∀ x, ‖b x‖ ≤ Mb)
    {u e : ℂ} {U : ℝ≥0 → Ω → ℂ}
    (hU : ∀ ω (t : ℝ≥0), U t ω = u + (∫ r in (0 : ℝ)..t, b (U r.toNNReal ω)) + B t ω • e)
    {F : ℂ → ℝ} {C : ℝ} (hF : ContDiff ℝ 3 F)
    (hD : ∀ x, ‖fderiv ℝ F x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 F x‖ ≤ C ∧
      ‖iteratedFDeriv ℝ 3 F x‖ ≤ C) (hFb : ∀ x, |F x| ≤ C)
    (hU0 : ∀ᵐ ω ∂P, U 0 ω = u)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) (T : ℝ≥0)
    (hτT : ∀ ω, τ ω ≤ T) :
    Integrable (fun ω => F (U (τ ω) ω) - F u
      - ∫ r in (0 : ℝ)..(τ ω), dynkinGen b e F (U r.toNNReal ω)) P ∧
    ∫ ω, (F (U (τ ω) ω) - F u
      - ∫ r in (0 : ℝ)..(τ ω), dynkinGen b e F (U r.toNNReal ω)) ∂P = 0 := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hC : 0 ≤ C := (abs_nonneg _).trans (hFb 0)
  set G : ℂ → ℝ := dynkinGen b e F with hGdef
  set CG : ℝ := C * Mb + 1 / 2 * (C * ‖e‖ ^ 2) with hCG
  have hGb : ∀ x, |G x| ≤ CG := abs_dynkinGen_le hC hbM hD
  have hGc : Continuous G := Dynkin.continuous_dynkinGen hF hb.continuous e
  have hUc : ∀ ω, Continuous (U · ω) := Dynkin.continuous_of_integralEq hBc hb.continuous hbM hU
  set M : ℝ≥0 → Ω → ℝ := fun t ω => F (U t ω) - F u
    - ∫ r in (0 : ℝ)..t, G (U r.toNNReal ω) with hMdef
  have hM : Martingale M 𝓕 P := Dynkin.dynkin_additive hB hBc 𝓕 hBad hpast hb hbM hU hF hD
  have hMT := martingale_min_const hM T
  have hprim : ∀ ω, Continuous fun t : ℝ => ∫ r in (0 : ℝ)..t, G (U r.toNNReal ω) := fun ω =>
    intervalIntegral.continuous_primitive (fun _ _ =>
      (hGc.comp ((hUc ω).comp continuous_real_toNNReal)).intervalIntegrable _ _) 0
  have hMc : ∀ ω, Continuous fun t => M (min t T) ω := by
    intro ω
    have h1 : Continuous fun t : ℝ≥0 => M t ω :=
      ((hF.continuous.comp (hUc ω)).sub continuous_const).sub
        ((hprim ω).comp NNReal.continuous_coe)
    exact h1.comp (continuous_id.min continuous_const)
  have hMb : ∀ t ω, |M (min t T) ω| ≤ 2 * C + CG * T := by
    intro t ω
    have hI : ‖∫ r in (0 : ℝ)..(min t T : ℝ≥0), G (U r.toNNReal ω)‖ ≤ CG * |((min t T : ℝ≥0) : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun r _ => by
        rw [Real.norm_eq_abs]; exact hGb _
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)] at hI
    have hmT : ((min t T : ℝ≥0) : ℝ) ≤ T := by exact_mod_cast min_le_right t T
    have hCG0 : 0 ≤ CG := (abs_nonneg _).trans (hGb 0)
    have := hFb (U (min t T) ω)
    have := hFb u
    simp only [hMdef]
    calc |F (U (min t T) ω) - F u - ∫ r in (0 : ℝ)..(min t T : ℝ≥0), G (U r.toNNReal ω)|
        ≤ |F (U (min t T) ω)| + |F u| + |∫ r in (0 : ℝ)..(min t T : ℝ≥0), G (U r.toNNReal ω)| := by
          have := abs_sub (F (U (min t T) ω) - F u) (∫ r in (0 : ℝ)..(min t T : ℝ≥0), G (U r.toNNReal ω))
          have := abs_sub (F (U (min t T) ω)) (F u)
          linarith
      _ ≤ C + C + CG * T := by gcongr; exact hI.trans (mul_le_mul_of_nonneg_left hmT hCG0)
      _ = 2 * C + CG * T := by ring
  have hS := ItoLite.martingale_stopped_of_continuous hMT hMc hMb hτ
  have hval : (fun ω => M (min (min T (τ ω)) T) ω) = fun ω => F (U (τ ω) ω) - F u
      - ∫ r in (0 : ℝ)..(τ ω), G (U r.toNNReal ω) := by
    funext ω
    rw [min_eq_right (hτT ω), min_eq_left (hτT ω)]
  have hint : Integrable (fun ω => M (min (min T (τ ω)) T) ω) P := hS.integrable T
  rw [hval] at hint
  refine ⟨hint, ?_⟩
  have h0 : ∫ ω, M (min (min (0 : ℝ≥0) (τ ω)) T) ω ∂P = 0 := by
    have : (fun ω => M (min (min (0 : ℝ≥0) (τ ω)) T) ω) =ᵐ[P] fun _ => (0 : ℝ) := by
      filter_upwards [hU0] with ω hω
      simp [hMdef, hω]
    rw [integral_congr_ae this, integral_zero]
  have hce := hS.2 0 T zero_le
  have h1 : ∫ ω, M (min (min T (τ ω)) T) ω ∂P = ∫ ω, M (min (min (0 : ℝ≥0) (τ ω)) T) ω ∂P := by
    rw [← integral_condExp (𝓕.le 0)]
    exact integral_congr_ae hce
  rw [← hval, h1, h0]

/-! ### Hitting times of closed sets by continuous paths -/

theorem hittingBtwn_mem_of_isClosed {X : ℝ≥0 → Ω → ℂ} {S : Set ℂ} (hS : IsClosed S) {ω : Ω}
    (hc : Continuous (X · ω)) {T : ℝ≥0} (hex : ∃ j ∈ Icc 0 T, X j ω ∈ S) :
    X (hittingBtwn X S 0 T ω) ω ∈ S := by
  classical
  rw [hittingBtwn_def]
  simp only [if_pos hex]
  obtain ⟨j, hj, hjS⟩ := hex
  have hcl : IsClosed (Icc 0 T ∩ {i : ℝ≥0 | X i ω ∈ S}) :=
    isClosed_Icc.inter (hS.preimage hc)
  exact (hcl.csInf_mem ⟨j, hj, hjS⟩ ⟨0, fun _ h => h.1.1⟩).2

theorem mem_of_le_of_forall_lt {X : ℝ≥0 → Ω → ℂ} {K : Set ℂ} (hK : IsClosed K) {ω : Ω}
    (hc : Continuous (X · ω)) {τ : ℝ≥0} (h0 : X 0 ω ∈ K) (hlt : ∀ t < τ, X t ω ∈ K) :
    ∀ t ≤ τ, X t ω ∈ K := by
  intro t ht
  rcases ht.lt_or_eq with h | rfl
  · exact hlt t h
  rcases eq_or_ne t 0 with h0' | hne
  · rw [h0']; exact h0
  have hsub : Ico 0 t ⊆ {r | X r ω ∈ K} := fun r hr => hlt r hr.2
  have hcl := closure_minimal hsub (hK.preimage hc)
  have : t ∈ closure (Ico 0 t) := by
    rw [closure_Ico (Ne.symm hne)]; exact ⟨zero_le, le_rfl⟩
  exact hcl this

/-! ### Deterministic facts on the tamed flow -/

/-- The exit set of the annular region. -/
def exitSet (ρ R c : ℝ) : Set ℂ := {z | ‖z‖ ≤ ρ} ∪ {z | R ≤ ‖z‖} ∪ {z | z.im ≤ c}

theorem isClosed_exitSet (ρ R c : ℝ) : IsClosed (exitSet ρ R c) :=
  ((isClosed_le continuous_norm continuous_const).union
    (isClosed_le continuous_const continuous_norm)).union
    (isClosed_le Complex.continuous_im continuous_const)

theorem notMem_exitSet_iff {ρ R c : ℝ} {z : ℂ} : z ∉ exitSet ρ R c ↔ z ∈ annOpen ρ R c := by
  simp only [exitSet, annOpen, mem_union, Set.mem_ofPred_eq, not_or, not_le]
  tauto

/-- While the tamed flow stays in `{|z| ≥ ρ, Im z ≥ c}` up to time `τ ≤ T`, the clock identity
forces `Im U_τ > c` (for `c` small). -/
theorem im_tamedZ_gt {W : ℝ → ℝ} (hW : Continuous W) {a : ℂ} {c ρ R T τ : ℝ} (hc : 0 < c)
    (hρ : 0 < ρ) (ha0 : 0 < a.im) (hcsmall : c < a.im * Real.exp (-2 * (T / ρ ^ 2)))
    (hτ0 : 0 ≤ τ) (hτT : τ ≤ T) (hK : ∀ s ∈ Icc 0 τ, tamedZ W c a s ∈ annReg ρ R c) :
    c < (tamedZ W c a τ).im := by
  have him : ∀ s ∈ Icc 0 τ, c ≤ (tamedZ W c a s).im := fun s hs => (hK s hs).2.2
  have hsol := isForwardSol_tamedZ hW hc hτ0 him
  rw [sol_im_eq_clock hW ha0 hsol ⟨hτ0, le_rfl⟩]
  have hint : ∫ s in (0 : ℝ)..τ, 1 / ‖tamedZ W c a s‖ ^ 2 ≤ T / ρ ^ 2 := by
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := τ)
      (C := 1 / ρ ^ 2) (f := fun s => 1 / ‖tamedZ W c a s‖ ^ 2) (fun s hs => by
        rw [uIoc_of_le hτ0] at hs
        have hρs := (hK s ⟨hs.1.le, hs.2⟩).1
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        gcongr)
    rw [sub_zero, abs_of_nonneg hτ0] at hI
    calc ∫ s in (0 : ℝ)..τ, 1 / ‖tamedZ W c a s‖ ^ 2
        ≤ ‖∫ s in (0 : ℝ)..τ, 1 / ‖tamedZ W c a s‖ ^ 2‖ := Real.le_norm_self _
      _ ≤ 1 / ρ ^ 2 * τ := hI
      _ ≤ 1 / ρ ^ 2 * T := by gcongr
      _ = T / ρ ^ 2 := by ring
  calc c < a.im * Real.exp (-2 * (T / ρ ^ 2)) := hcsmall
    _ ≤ a.im * Real.exp (-2 * ∫ s in (0 : ℝ)..τ, 1 / ‖tamedZ W c a s‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) ha0.le

/-- If `a ∈ K_T`, the tamed flow leaves the open annular region before time `T`. -/
theorem exists_exit_of_mem_fwdHull {W : ℝ → ℝ} (hW : Continuous W) {a : ℂ} {c ρ R T : ℝ}
    (hc : 0 < c) (hρ : 0 < ρ) (hmem : a ∈ fwdHull W T) :
    ∃ s ∈ Icc 0 T, tamedZ W c a s ∉ annOpen ρ R c := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ha0, σ, hσT, -, hcl⟩ := (mem_fwdHull_iff_clock hW).1 hmem
  obtain ⟨t, ht0, htσ, hM⟩ := hcl (T / ρ ^ 2)
  have htT : t ≤ T := htσ.le.trans hσT
  have him : ∀ s ∈ Icc (0 : ℝ) t, c ≤ (tamedZ W c a s).im := fun s hs =>
    (hcon s ⟨hs.1, hs.2.trans htT⟩).2.2.le
  obtain ⟨-, heq⟩ := fwdMap_eq_tamedZ hW hc ht0 ha0 him
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (C := 1 / ρ ^ 2) (f := fun s => 1 / ‖fwdMap W s a‖ ^ 2) (fun s hs => by
      rw [uIoc_of_le ht0] at hs
      have hs' : s ∈ Icc 0 t := ⟨hs.1.le, hs.2⟩
      rw [heq s hs']
      have hρs := (hcon s ⟨hs'.1, hs'.2.trans htT⟩).1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr)
  rw [sub_zero, abs_of_nonneg ht0] at hI
  have : fwdClock W t a ≤ T / ρ ^ 2 :=
    calc fwdClock W t a ≤ ‖fwdClock W t a‖ := Real.le_norm_self _
      _ ≤ 1 / ρ ^ 2 * t := hI
      _ ≤ 1 / ρ ^ 2 * T := by gcongr
      _ = T / ρ ^ 2 := by ring
  linarith

/-! ### The one-point bound -/

theorem lyapV_ge {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (ε : ℝ) {z : ℂ} (hz : 0 < z.im) :
    -Real.log ‖z‖ + ε * ‖z‖ ^ 2 - (4 - κ) / 4 * (2 * Real.pi ^ 2 / κ) ≤ lyapV κ ε z := by
  have := (abs_le.1 (abs_lyapV_sub_le hκ hκ4 ε hz)).1
  linarith

theorem lyapV_le {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (ε : ℝ) {z : ℂ} (hz : 0 < z.im) :
    lyapV κ ε z ≤ -Real.log ‖z‖ + ε * ‖z‖ ^ 2 + (4 - κ) / 4 * (2 * Real.pi ^ 2 / κ) := by
  have := (abs_le.1 (abs_lyapV_sub_le hκ hκ4 ε hz)).2
  linarith

/-- **DF-1/DF-2, one-point estimate.** For `a` in the open annular region, with `c` below the
clock bound, `P(a ∈ K_T) ≤ Q/m` where `Q = V(a) + Tε(κ+4) + log R + C_g` and
`m = min(log R − log ρ, εR²)`. -/
theorem prob_exit_le (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    {a : ℂ} {ρ R c ε : ℝ} (T : ℝ≥0) (hρ : 0 < ρ) (hρR : ρ < R) (hc : 0 < c) (hε : 0 < ε)
    (ha : a ∈ annOpen ρ R c) (hcsmall : c < a.im * Real.exp (-2 * ((T : ℝ) / ρ ^ 2))) :
    P {ω | B 0 ω = 0 ∧ ∃ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∉ annOpen ρ R c}
      ≤ ENNReal.ofReal
      ((lyapV κ ε a + T * (ε * (κ + 4)) + Real.log R + (4 - κ) / 4 * (2 * Real.pi ^ 2 / κ))
        / min (Real.log R - Real.log ρ) (ε * R ^ 2)) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hR : 0 < R := hρ.trans hρR
  set μG : ℝ := (4 - κ) / 4 * (2 * Real.pi ^ 2 / κ) with hμG
  set e : ℂ := -((Real.sqrt κ : ℝ) : ℂ) with he
  set 𝓕 := bmFilt hBm with h𝓕
  set U : ℝ≥0 → Ω → ℂ := fun t ω => tamedZ (drive κ B ω) c a t with hUdef
  have hU : ∀ ω (t : ℝ≥0),
      U t ω = a + (∫ r in (0 : ℝ)..t, tamedZField c (U r.toNNReal ω)) + B t ω • e :=
    fun ω t => tamedZ_integralEq hBc hc κ a ω t
  have hbM : ∀ x, ‖tamedZField c x‖ ≤ 2 / c := norm_tamedZField_le hc
  have hb := lipschitz_tamedZField hc
  have hUc : ∀ ω, Continuous (U · ω) :=
    Dynkin.continuous_of_integralEq hBc hb.continuous hbM hU
  have hUm : ∀ t, Measurable[𝓕 t] (U t) :=
    Dynkin.measurable_of_integralEq 𝓕 (bmFilt_adapted hBm) hBc hb hbM hU hUc
  obtain ⟨F, C, hF, hFC, hFV⟩ := exists_lyap_cutoff κ ε hρ hR hc
  set E := exitSet ρ R c with hE
  set τ : Ω → ℝ≥0 := hittingBtwn U E 0 T with hτdef
  have hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)) :=
    ItoLite.isStoppingTime_hittingBtwn_of_isClosed hUm hUc (isClosed_exitSet ρ R c) T
  have hτT : ∀ ω, τ ω ≤ T := fun ω => hittingBtwn_le ω
  have hB0 := hB.eval_zero_ae_eq_zero
  have hU0' : ∀ ω, B 0 ω = 0 → U 0 ω = a := by
    intro ω hω; rw [hU ω 0]; simp [hω]
  have hU0 : ∀ᵐ ω ∂P, U 0 ω = a := by
    filter_upwards [hB0] with ω hω using hU0' ω hω
  obtain ⟨hint, hzero⟩ := dynkin_stopped hB hBc 𝓕 (bmFilt_adapted hBm) (bmFilt_le_past hBm)
    hb hbM hU hF (fun x => (hFC x).2) (fun x => (hFC x).1) hU0 hτ T hτT
  -- the path stays in the closed region up to `τ`
  have hK : ∀ ω, B 0 ω = 0 → ∀ t ≤ τ ω, U t ω ∈ annReg ρ R c := by
    intro ω hω
    refine mem_of_le_of_forall_lt (isClosed_annReg ρ R c) (hUc ω) ?_ ?_
    · rw [hU0' ω hω]; exact annOpen_subset_annReg ha
    · intro t ht
      exact annOpen_subset_annReg
        (notMem_exitSet_iff.1 (notMem_of_lt_hittingBtwn ht zero_le))
  have hKim : ∀ ω, B 0 ω = 0 → ∀ t ≤ τ ω, 0 < (U t ω).im := fun ω hω t ht =>
    hc.trans_le (hK ω hω t ht).2.2
  -- the generator bound along the stopped path
  have hGint : ∀ ω, B 0 ω = 0 →
      ∫ r in (0 : ℝ)..(τ ω), dynkinGen (tamedZField c) e F (U r.toNNReal ω)
        ≤ T * (ε * (κ + 4)) := by
    intro ω hω
    have hGc : Continuous fun r : ℝ => dynkinGen (tamedZField c) e F (U r.toNNReal ω) :=
      (Dynkin.continuous_dynkinGen hF hb.continuous e).comp ((hUc ω).comp continuous_real_toNNReal)
    have hmono := intervalIntegral.integral_mono_on (NNReal.coe_nonneg (τ ω))
      (hGc.intervalIntegrable (μ := volume) _ _)
      (continuous_const.intervalIntegrable (μ := volume) (u := fun _ => ε * (κ + 4)) _ _)
      (fun r hr => by
        have hle : r.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.2 hr.2
        have hmem := hK ω hω _ hle
        have him := hKim ω hω _ hle
        rw [dynkinGen_congr (hFV _ hmem)]
        refine (dynkinGen_lyapV_le hκ hε.le hmem.2.2 him).trans ?_
        have : -(4 - κ) / (2 * ‖U r.toNNReal ω‖ ^ 2) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
        linarith)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
    have hτT' : ((τ ω : ℝ≥0) : ℝ) ≤ T := by exact_mod_cast hτT ω
    have hpos : 0 ≤ ε * (κ + 4) := by positivity
    nlinarith
  -- measurability of `F(U_τ)`
  have hτm : Measurable τ := by
    refine measurable_of_Iic fun x => ?_
    have h := 𝓕.le x _ (hτ x)
    have e : τ ⁻¹' Iic x = {ω | ((τ ω : ℝ≥0) : WithTop ℝ≥0) ≤ (x : WithTop ℝ≥0)} := by
      ext ω; simp only [mem_preimage, mem_Iic]; exact WithTop.coe_le_coe.symm
    rw [e]; exact h
  have hUj : Measurable (Function.uncurry U) :=
    measurable_uncurry_of_continuous_of_measurable hUc fun t => (hUm t).mono (𝓕.le t) le_rfl
  have hFUm : Measurable fun ω => F (U (τ ω) ω) :=
    hF.continuous.measurable.comp (hUj.comp (hτm.prodMk measurable_id))
  have hFUi : Integrable (fun ω => F (U (τ ω) ω)) P :=
    ItoLite.integrable_of_bound_abs hFUm.stronglyMeasurable fun ω => (hFC _).1
  -- `E F(U_τ) ≤ F(a) + Tε(κ+4)`
  have hFa : F a = lyapV κ ε a := (hFV a (annOpen_subset_annReg ha)).eq_of_nhds
  have hEF : ∫ ω, F (U (τ ω) ω) ∂P ≤ F a + T * (ε * (κ + 4)) := by
    have hle : ∀ᵐ ω ∂P, F (U (τ ω) ω) ≤ (F (U (τ ω) ω) - F a
        - ∫ r in (0 : ℝ)..(τ ω), dynkinGen (tamedZField c) e F (U r.toNNReal ω))
        + (F a + T * (ε * (κ + 4))) := by
      filter_upwards [hB0] with ω hω
      have := hGint ω hω
      linarith
    have h1 : ∫ ω, F (U (τ ω) ω) ∂P ≤ ∫ ω, ((F (U (τ ω) ω) - F a
        - ∫ r in (0 : ℝ)..(τ ω), dynkinGen (tamedZField c) e F (U r.toNNReal ω))
        + (F a + T * (ε * (κ + 4)))) ∂P :=
      integral_mono_ae hFUi (hint.add (integrable_const (F a + T * (ε * (κ + 4))))) hle
    rw [integral_add hint (integrable_const _), hzero, integral_const] at h1
    simpa using h1
  -- the nonnegative variable `Y`
  set Y : Ω → ℝ := fun ω => F (U (τ ω) ω) + Real.log R + μG with hYdef
  have hFUV : ∀ ω, B 0 ω = 0 → F (U (τ ω) ω) = lyapV κ ε (U (τ ω) ω) := fun ω hω =>
    (hFV _ (hK ω hω _ le_rfl)).eq_of_nhds
  have hYnn : 0 ≤ᵐ[P] Y := by
    filter_upwards [hB0] with ω hω
    have hmem := hK ω hω _ le_rfl
    have hge := lyapV_ge hκ hκ4 ε (hKim ω hω _ le_rfl)
    have hn0 : 0 < ‖U (τ ω) ω‖ := hρ.trans_le hmem.1
    have hlog : Real.log ‖U (τ ω) ω‖ ≤ Real.log R := Real.log_le_log hn0 hmem.2.1
    have : 0 ≤ ε * ‖U (τ ω) ω‖ ^ 2 := by positivity
    show 0 ≤ F (U (τ ω) ω) + Real.log R + μG
    rw [hFUV ω hω]
    linarith
  have hYi : Integrable Y P := (hFUi.add (integrable_const _)).add (integrable_const _)
  set m : ℝ := min (Real.log R - Real.log ρ) (ε * R ^ 2) with hm
  have hm0 : 0 < m := lt_min (by linarith [Real.log_lt_log hρ hρR]) (by positivity)
  have hEY : ∫ ω, Y ω ∂P ≤ lyapV κ ε a + T * (ε * (κ + 4)) + Real.log R + μG := by
    have : ∫ ω, Y ω ∂P = ∫ ω, F (U (τ ω) ω) ∂P + Real.log R + μG := by
      have i1 : Integrable (fun ω => F (U (τ ω) ω) + Real.log R) P :=
        hFUi.add (integrable_const _)
      simp only [hYdef]
      rw [integral_add i1 (integrable_const _), integral_add hFUi (integrable_const _)]
      simp
    rw [this, ← hFa]; linarith
  have hMarkov := mul_meas_ge_le_integral_of_nonneg hYnn hYi m
  -- the event inclusion
  have hsub : {ω | B 0 ω = 0 ∧ ∃ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∉ annOpen ρ R c}
      ⊆ {ω | m ≤ Y ω} := by
    rintro ω ⟨hB0ω, s, hs, hsnot⟩
    have hW := continuous_drive_ns hBc κ ω
    have hsE : U s.toNNReal ω ∈ E := by
      have : tamedZ (drive κ B ω) c a (s.toNNReal : ℝ) ∉ annOpen ρ R c := by
        rw [Real.coe_toNNReal s hs.1]; exact hsnot
      by_contra hcon
      exact this (notMem_exitSet_iff.1 hcon)
    have hτE : U (τ ω) ω ∈ E := hittingBtwn_mem_of_isClosed (isClosed_exitSet ρ R c) (hUc ω)
      ⟨s.toNNReal, ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hs.2⟩, hsE⟩
    have hmem := hK ω hB0ω _ le_rfl
    have hgt : c < (U (τ ω) ω).im := by
      refine im_tamedZ_gt (R := R) hW hc hρ (hc.trans ha.2.2) hcsmall (NNReal.coe_nonneg _)
        (by exact_mod_cast hτT ω) (fun s hs => ?_)
      have hle : s.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.2 hs.2
      have := hK ω hB0ω _ hle
      simp only [hUdef, Real.coe_toNNReal s hs.1] at this
      exact this
    have hge := lyapV_ge hκ hκ4 ε (hKim ω hB0ω _ le_rfl)
    show m ≤ F (U (τ ω) ω) + Real.log R + μG
    rw [hFUV ω hB0ω]
    have hn0 : 0 < ‖U (τ ω) ω‖ := hρ.trans_le hmem.1
    rcases hτE with (h1 | h2) | h3
    · -- exit through the small circle
      have hlog : Real.log ‖U (τ ω) ω‖ ≤ Real.log ρ := Real.log_le_log hn0 h1
      have : 0 ≤ ε * ‖U (τ ω) ω‖ ^ 2 := by positivity
      have := min_le_left (Real.log R - Real.log ρ) (ε * R ^ 2)
      linarith
    · -- exit through the large circle
      have heq : ‖U (τ ω) ω‖ = R := le_antisymm hmem.2.1 h2
      rw [heq] at hge
      have := min_le_right (Real.log R - Real.log ρ) (ε * R ^ 2)
      linarith
    · exact absurd h3 (not_le.2 hgt)
  calc P {ω | B 0 ω = 0 ∧ ∃ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∉ annOpen ρ R c}
      ≤ P {ω | m ≤ Y ω} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | m ≤ Y ω}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal ((lyapV κ ε a + T * (ε * (κ + 4)) + Real.log R + μG) / m) := by
        apply ENNReal.ofReal_le_ofReal
        rw [le_div_iff₀ hm0]
        linarith

/-- **DF-1/DF-2, one-point estimate for the hull.** -/
theorem prob_mem_fwdHull_le (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    {a : ℂ} {ρ R c ε : ℝ} (T : ℝ≥0) (hρ : 0 < ρ) (hρR : ρ < R) (hc : 0 < c) (hε : 0 < ε)
    (ha : a ∈ annOpen ρ R c) (hcsmall : c < a.im * Real.exp (-2 * ((T : ℝ) / ρ ^ 2))) :
    P {ω | a ∈ fwdHull (drive κ B ω) T} ≤ ENNReal.ofReal
      ((lyapV κ ε a + T * (ε * (κ + 4)) + Real.log R + (4 - κ) / 4 * (2 * Real.pi ^ 2 / κ))
        / min (Real.log R - Real.log ρ) (ε * R ^ 2)) := by
  have hnull : P {ω | ¬ B 0 ω = 0} = 0 := ae_iff.1 hB.eval_zero_ae_eq_zero
  have hsub : {ω | a ∈ fwdHull (drive κ B ω) T} ⊆
      {ω | B 0 ω = 0 ∧ ∃ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∉ annOpen ρ R c}
        ∪ {ω | ¬ B 0 ω = 0} := by
    intro ω hω
    by_cases h : B 0 ω = 0
    · exact Or.inl ⟨h, exists_exit_of_mem_fwdHull (R := R) (continuous_drive_ns hBc κ ω) hc hρ hω⟩
    · exact Or.inr h
  calc P {ω | a ∈ fwdHull (drive κ B ω) T}
      ≤ P ({ω | B 0 ω = 0 ∧ ∃ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∉ annOpen ρ R c}
        ∪ {ω | ¬ B 0 ω = 0}) := measure_mono hsub
    _ ≤ P {ω | B 0 ω = 0 ∧ ∃ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∉ annOpen ρ R c}
        + P {ω | ¬ B 0 ω = 0} := measure_union_le _ _
    _ ≤ _ := by rw [hnull, add_zero]; exact prob_exit_le hB hBm hBc hκ hκ4 T hρ hρR hc hε ha hcsmall

/-- **DF-2 (non-swallowing).** For `κ ∈ (0,4]` and a fixed `a ∈ ℍ`, a.s. `a ∉ K_T`. -/
theorem prob_mem_fwdHull_eq_zero (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    {a : ℂ} (ha : 0 < a.im) (T : ℝ) :
    P {ω | a ∈ fwdHull (drive κ B ω) T} = 0 := by
  set Tn : ℝ≥0 := T.toNNReal with hTn
  have hsub : {ω | a ∈ fwdHull (drive κ B ω) T} ⊆ {ω | a ∈ fwdHull (drive κ B ω) Tn} :=
    fun ω hω => fwdHull_mono.1 (Real.le_coe_toNNReal T) hω
  refine le_antisymm ((measure_mono hsub).trans ?_) zero_le
  set μG : ℝ := (4 - κ) / 4 * (2 * Real.pi ^ 2 / κ) with hμG
  set A : ℝ := -Real.log ‖a‖ + 2 * μG with hA
  set Bc : ℝ := ‖a‖ ^ 2 + (Tn : ℝ) * (κ + 4) with hBc'
  set f : ℝ → ℝ := fun R => A / R + Bc / R / R + Real.log R / R with hf
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => A / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun R : ℝ => Bc / R / R) atTop (𝓝 0) :=
      (tendsto_const_nhds.div_atTop tendsto_id).div_atTop tendsto_id
    have h3 : Tendsto (fun R : ℝ => Real.log R / R) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    simpa using (h1.add h2).add h3
  have hna : 0 < ‖a‖ := norm_pos_iff.2 (fun h => by simp [h] at ha)
  have hev : ∀ᶠ R in atTop, P {ω | a ∈ fwdHull (drive κ B ω) Tn} ≤ ENNReal.ofReal (f R) := by
    filter_upwards [eventually_gt_atTop (max 1 (max ‖a‖ (-Real.log ‖a‖)))] with R hR
    have hR1 : 1 < R := (le_max_left _ _).trans_lt hR
    have hRa : ‖a‖ < R := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hR
    have hRl : -Real.log ‖a‖ < R := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hR
    set ρ : ℝ := Real.exp (-R) with hρdef
    have hρ : 0 < ρ := Real.exp_pos _
    have hρa : ρ < ‖a‖ := by
      rw [hρdef, ← Real.exp_log hna]; exact Real.exp_lt_exp.2 (by linarith)
    have hρR : ρ < R := hρa.trans hRa
    set c : ℝ := a.im * Real.exp (-2 * ((Tn : ℝ) / ρ ^ 2)) / 2 with hcdef
    have hpos : 0 < a.im * Real.exp (-2 * ((Tn : ℝ) / ρ ^ 2)) := by positivity
    have hc : 0 < c := by positivity
    have hcs : c < a.im * Real.exp (-2 * ((Tn : ℝ) / ρ ^ 2)) := by linarith
    have hexp : Real.exp (-2 * ((Tn : ℝ) / ρ ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ (Tn : ℝ) / ρ ^ 2 := by positivity
      linarith
    have hca : c < a.im := hcs.trans_le (mul_le_of_le_one_right ha.le hexp)
    have haO : a ∈ annOpen ρ R c := ⟨hρa, hRa, hca⟩
    have hε : 0 < 1 / R := by positivity
    refine (prob_mem_fwdHull_le hB hBm hBc hκ hκ4 Tn hρ hρR hc hε haO hcs).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hlogρ : Real.log ρ = -R := Real.log_exp _
    have hRR : 1 / R * R ^ 2 = R := by field_simp
    have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1.le
    have hm : min (Real.log R - Real.log ρ) (1 / R * R ^ 2) = R := by
      rw [hlogρ, hRR]; apply min_eq_right; linarith
    rw [hm, div_le_iff₀ (by linarith)]
    have hfR : f R * R = A + Bc / R + Real.log R := by
      simp only [hf]; field_simp
    rw [hfR]
    have hV := lyapV_le hκ hκ4 (1 / R) ha
    have e : Bc / R = 1 / R * ‖a‖ ^ 2 + (Tn : ℝ) * (1 / R * (κ + 4)) := by
      simp only [hBc']; ring
    rw [e, hA]
    linarith
  have hlim' : Tendsto (fun R => ENNReal.ofReal (f R)) atTop (𝓝 (ENNReal.ofReal 0)) :=
    ENNReal.tendsto_ofReal hlim
  simpa using ge_of_tendsto hlim' hev

/-- A countable characterization of the hull through tamed flows, used for measurability. -/
theorem mem_fwdHull_iff_tamed {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {a : ℂ} :
    a ∈ fwdHull W T ↔ 0 < a.im ∧ ∀ k : ℕ, ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T ∧
      (tamedZ W (1 / ((k : ℝ) + 1)) a q).im < 2 * (1 / ((k : ℝ) + 1)) := by
  constructor
  · intro hmem
    obtain ⟨ha0, σ, hσT, -, hinf⟩ := (mem_fwdHull_iff_inf_im hW).1 hmem
    refine ⟨ha0, fun k => ?_⟩
    set c : ℝ := 1 / ((k : ℝ) + 1) with hcdef
    have hc : 0 < c := by positivity
    have hex : ∃ s, 0 ≤ s ∧ s < T ∧ (tamedZ W c a s).im < 2 * c := by
      obtain ⟨t, ht0, htσ, hlt⟩ := hinf c hc
      have htT : t < T := htσ.trans_le hσT
      by_cases hall : ∀ s ∈ Icc (0 : ℝ) t, c ≤ (tamedZ W c a s).im
      · obtain ⟨-, heq⟩ := fwdMap_eq_tamedZ hW hc ht0 ha0 hall
        refine ⟨t, ht0, htT, ?_⟩
        rw [← heq t ⟨ht0, le_rfl⟩]; linarith
      · push Not at hall
        obtain ⟨s, hs, hslt⟩ := hall
        exact ⟨s, hs.1, hs.2.trans_lt htT, by linarith⟩
    obtain ⟨s, hs0, hsT, hslt⟩ := hex
    have hcont := continuousOn_tamedZ hW hc hT a s ⟨hs0, hsT.le⟩
    have hcont' : ContinuousWithinAt (fun r => (tamedZ W c a r).im) (Icc 0 T) s :=
      Complex.continuous_im.continuousAt.comp_continuousWithinAt hcont
    have hev : ∀ᶠ r in 𝓝[Icc 0 T] s, (tamedZ W c a r).im < 2 * c :=
      Filter.Tendsto.eventually hcont' (gt_mem_nhds hslt)
    obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhdsWithin_iff.1 hev
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min (by linarith : s < s + δ) hsT)
    have hqI : (q : ℝ) ∈ Icc 0 T := ⟨by linarith, (hq2.trans_le (min_le_right _ _)).le⟩
    refine ⟨q, hqI.1, hqI.2, hδball ⟨?_, hqI⟩⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [min_le_left (s + δ) T]
  · rintro ⟨ha0, hk⟩
    by_contra hK
    obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hT ha0 hK
    obtain ⟨s0, hs0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT)
      (Complex.continuous_im.comp_continuousOn hu.1)
    have hm : 0 < (u s0).im := sol_im_pos hW ha0 hu hs0
    obtain ⟨k, hk'⟩ := exists_nat_one_div_lt (half_pos hm)
    set c : ℝ := 1 / ((k : ℝ) + 1) with hcdef
    have hc : 0 < c := by positivity
    have hmin' : ∀ t ∈ Icc (0 : ℝ) T, (u s0).im ≤ (u t).im := fun t ht => by
      have := isMinOn_iff.1 hmin t ht
      simpa using this
    have him : ∀ t ∈ Icc (0 : ℝ) T, c ≤ (u t).im := fun t ht => by
      have := hmin' t ht; linarith
    have heq := tamedZ_eq_of_isForwardSol hW hc hT hu him
    obtain ⟨q, hq0, hqT, hq⟩ := hk k
    rw [heq q ⟨hq0, hqT⟩] at hq
    have := hmin' q ⟨hq0, hqT⟩
    linarith

theorem measurableSet_fwdHull_prod (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    MeasurableSet {p : ℂ × Ω | p.1 ∈ fwdHull (drive κ B p.2) T} := by
  have e : {p : ℂ × Ω | p.1 ∈ fwdHull (drive κ B p.2) T} = {p : ℂ × Ω | 0 < p.1.im} ∩
      ⋂ k : ℕ, ⋃ q : ℚ, ⋃ (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
        {p : ℂ × Ω | (tamedZ (drive κ B p.2) (1 / ((k : ℝ) + 1)) p.1 q).im
          < 2 * (1 / ((k : ℝ) + 1))} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion, exists_prop,
      mem_fwdHull_iff_tamed (continuous_drive_ns hBc κ p.2) hT, and_assoc]
  rw [e]
  refine (measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_fst)).inter
    (MeasurableSet.iInter fun k => MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq =>
      measurableSet_lt (Complex.measurable_im.comp
        (measurable_tamed_drive κ (by positivity) B hBc hq.1 (fun r _ => hBm r)).1)
        measurable_const)

/-- **DF-2 (zero area).** For `κ ∈ (0,4]`, a.s. the hull `K_T` is null for any s-finite
measure `ν` on `ℂ` fixed in advance (Lebesgue measure, or the uniform measure on a circle). -/
theorem ae_measure_fwdHull_eq_zero (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (ν : Measure ℂ) [SFinite ν] (T : ℝ) :
    ∀ᵐ ω ∂P, ν (fwdHull (drive κ B ω) T) = 0 := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set T' : ℝ := max T 0 with hT'
  suffices h : ∀ᵐ ω ∂P, ν (fwdHull (drive κ B ω) T') = 0 by
    filter_upwards [h] with ω hω
    exact measure_mono_null (fwdHull_mono.1 (le_max_left T 0)) hω
  set S : Set (Ω × ℂ) := {p | p.2 ∈ fwdHull (drive κ B p.1) T'} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_fwdHull_prod hBm hBc κ (le_max_right T 0)).preimage measurable_swap
  have h0 : (P.prod ν) S = 0 := by
    rw [Measure.prod_apply_symm hS]
    have hsec : ∀ a : ℂ, P ((fun ω => (ω, a)) ⁻¹' S) = 0 := by
      intro a
      by_cases ha : 0 < a.im
      · exact prob_mem_fwdHull_eq_zero hB hBm hBc hκ hκ4 ha T'
      · have : (fun ω => (ω, a)) ⁻¹' S = ∅ := by
          ext ω
          simp only [hSdef, mem_preimage, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false]
          exact fun h => ha h.1
        rw [this, measure_empty]
    simp [hsec]
  filter_upwards [(Measure.measure_prod_null hS).1 h0] with ω hω using hω

/-- **DF-2 (zero area), Lebesgue measure.** -/
theorem ae_volume_fwdHull_eq_zero (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (T : ℝ) :
    ∀ᵐ ω ∂P, volume (fwdHull (drive κ B ω) T) = 0 :=
  ae_measure_fwdHull_eq_zero hB hBm hBc hκ hκ4 volume T

end NonSwallow
end QuantumZipper
