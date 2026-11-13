/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm11.FrozenLocalDynkin at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Dynkin
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.OptionalStopping
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Local Dynkin formula with stopping (tool for MF-1, MF-2)

Blueprint `blueprint/THM11_BLUEPRINT.md`, §6 (MF-1, MF-2). The IL-3 Dynkin formula
(`Dynkin.dynkin_additive`) needs a globally `C³` test function with bounded derivatives. The
frozen fields are smooth only on an open set `O` (e.g. `{Im z > c}`), and are bounded only on
the region `K` visited before freezing. This file localizes Dynkin's formula:

* `FrozenMart.martingale_localDynkin_stopped`: if `F` is `C³` on an open `O`, the generator
  `dynkinGen b e F` vanishes on `K \ Cl` (with `K ⊆ O` closed), `F` is bounded on `K`, and the
  solution `U` stays in `K` up to (and including) its hitting time `τ` of the closed set `Cl`
  (capped at `T`), then `t ↦ F (U_{t ∧ τ})` is a martingale.

Proof: multiply `F` by smooth cutoffs `f_R` equal to `1` near `K ∩ closedBall 0 R` and supported
in `O` (smooth Urysohn), apply `dynkin_additive`, freeze at `T`, stop at the hitting time of
`Cl ∪ {‖x‖ ≥ R}` (IL-4), and let `R → ∞` by dominated convergence (the stopped values are
bounded by the bound of `F` on `K`, uniformly in `R`).

Also: `fderiv_apply_eq_deriv_line` and `iteratedFDeriv_two_eq_deriv_deriv_line`, which reduce
the generator to one-variable derivatives along lines.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace QuantumZipper
namespace FrozenMart

/-! ### Derivatives along lines -/

section Lines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_line (x v : E) (s : ℝ) : HasDerivAt (fun r : ℝ => x + r • v) v s := by
  simpa using ((hasDerivAt_id s).smul_const v).const_add x

/-- `DF(x)v` is the derivative at `0` of `s ↦ F(x + s v)`. -/
theorem fderiv_apply_eq_deriv_line {F : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x) (v : E) :
    fderiv ℝ F x v = deriv (fun s : ℝ => F (x + s • v)) 0 := by
  have h : HasDerivAt (fun s : ℝ => F (x + s • v)) (fderiv ℝ F x v) 0 :=
    hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line x v 0) (by simp)
  exact h.deriv.symm

/-- `D²F(x)[e,e]` is the second derivative at `0` of `r ↦ F(x + r e)`. -/
theorem iteratedFDeriv_two_eq_deriv_deriv_line {F : E → ℝ} {x : E} (hF : ContDiffAt ℝ 2 F x)
    (e : E) : iteratedFDeriv ℝ 2 F x ![e, e] = deriv (deriv (fun r : ℝ => F (x + r • e))) 0 := by
  rw [Dynkin.iteratedFDeriv_two_vec]
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 F y := hF.eventually (by simp)
  have hline : Tendsto (fun r : ℝ => x + r • e) (𝓝 0) (𝓝 x) := by
    have := (hasDerivAt_line x e 0).continuousAt.tendsto
    simpa using this
  have hev' : ∀ᶠ r in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 F (x + r • e) := hline.eventually hev
  have hderiv : deriv (fun r : ℝ => F (x + r • e)) =ᶠ[𝓝 0]
      fun r => fderiv ℝ F (x + r • e) e := by
    filter_upwards [hev'] with r hr
    have hd : DifferentiableAt ℝ F (x + r • e) := hr.differentiableAt (by norm_num)
    exact (hd.hasFDerivAt.comp_hasDerivAt_of_eq r (hasDerivAt_line x e r) rfl).deriv
  rw [hderiv.deriv_eq]
  have h1 : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : HasDerivAt (fun r : ℝ => fderiv ℝ F (x + r • e)) (fderiv ℝ (fderiv ℝ F) x e) 0 :=
    h1.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line x e 0) (by simp)
  have h4 := h2.clm_apply (hasDerivAt_const (0 : ℝ) e)
  simp only [map_zero, add_zero] at h4
  exact h4.deriv.symm

end Lines

/-! ### Smooth cutoffs -/

section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A smooth `[0,1]`-valued cutoff with compact support inside the open set `O`, equal to `1`
near the compact set `S ⊆ O`. -/
theorem exists_cutoff_of_isCompact {S O : Set E} (hS : IsCompact S) (hO : IsOpen O)
    (hSO : S ⊆ O) :
    ∃ f : E → ℝ, ContDiff ℝ 3 f ∧ (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport f ∧
      tsupport f ⊆ O ∧ ∀ x ∈ S, f =ᶠ[𝓝 x] 1 := by
  obtain ⟨η, hη, hηO⟩ := hS.exists_cthickening_subset_open hO hSO
  obtain ⟨f, hfd, hfr, hfs, hf1⟩ := exists_contDiff_support_eq_eq_one_iff (n := 3)
    (isOpen_thickening (δ := η) (E := S)) (isClosed_cthickening (δ := η / 2) (E := S))
    (cthickening_subset_thickening' hη (by linarith) S)
  have hts : tsupport f ⊆ cthickening η S := by
    rw [tsupport, hfs]; exact closure_thickening_subset_cthickening η S
  refine ⟨f, by exact_mod_cast hfd, fun x => hfr (mem_range_self x), ?_, hts.trans hηO, ?_⟩
  · exact (hS.cthickening (r := η)).of_isClosed_subset (isClosed_tsupport f) hts
  · intro x hx
    have hmem : thickening (η / 2) S ∈ 𝓝 x :=
      isOpen_thickening.mem_nhds (self_subset_thickening (by linarith) S hx)
    filter_upwards [hmem] with y hy
    exact (hf1 y).1 (thickening_subset_cthickening _ _ hy)

end Cutoff

/-! ### Local Dynkin formula with stopping -/

section LocalDynkin

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A martingale frozen at a deterministic time is a martingale. -/
theorem martingale_min_const [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M 𝓕 P) (T : ℝ≥0) : Martingale (fun t => M (min t T)) 𝓕 P := by
  refine ⟨fun t => (hM.stronglyAdapted (min t T)).mono (𝓕.mono (min_le_left t T)),
    fun s t hst => ?_⟩
  rcases le_total T s with h | h
  · have hs : min s T = T := min_eq_right h
    have ht : min t T = T := min_eq_right (h.trans hst)
    simp only [hs, ht]
    rw [condExp_of_stronglyMeasurable (𝓕.le s) ((hM.stronglyAdapted T).mono (𝓕.mono h))
      (hM.integrable T)]
  · have hs : min s T = s := min_eq_left h
    simp only [hs]
    exact hM.2 s (min t T) (le_min hst h)

/-- **Local Dynkin formula with stopping.** Let `U` solve `U_t = u + ∫₀ᵗ b(U) + B_t e` (`b`
bounded Lipschitz), let `F` be `C³` on the open set `O`, with `dynkinGen b e F = 0` on `K \ Cl`,
where `K ⊆ O` is closed, `Cl` is closed, and `|F| ≤ M` on `K`. If `U` stays in `K` up to (and
including) each time before which it has not met `Cl` (up to `T`), then, with
`τ = hittingBtwn U Cl 0 T`, the process `t ↦ F(U_{t ∧ τ})` is a martingale. -/
theorem martingale_localDynkin_stopped (hB : IsPreBrownianReal B P)
    (hBc : ∀ ω, Continuous (B · ω))
    (𝓕 : Filtration ℝ≥0 mΩ) (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hpast : ∀ t, 𝓕 t ≤ MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi)
    {b : E → E} {Lb : ℝ≥0} {Mb : ℝ} (hb : LipschitzWith Lb b) (hbM : ∀ x, ‖b x‖ ≤ Mb)
    {u e : E} {U : ℝ≥0 → Ω → E}
    (hU : ∀ ω (t : ℝ≥0), U t ω = u + (∫ r in (0 : ℝ)..t, b (U r.toNNReal ω)) + B t ω • e)
    {O Cl K : Set E} (hO : IsOpen O) (hCl : IsClosed Cl) (hK : IsClosed K) (hKO : K ⊆ O)
    {F : E → ℝ} (hF : ContDiffOn ℝ 3 F O) (hLF : ∀ x ∈ K, x ∉ Cl → dynkinGen b e F x = 0)
    (T : ℝ≥0) (hUK : ∀ ω (t : ℝ≥0), t ≤ T → (∀ s < t, U s ω ∉ Cl) → U t ω ∈ K)
    {M : ℝ} (hFM : ∀ x ∈ K, |F x| ≤ M) :
    Martingale (fun t ω => F (U (min t (hittingBtwn U Cl 0 T ω)) ω)) 𝓕 P := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hbc : Continuous b := hb.continuous
  have hUc : ∀ ω, Continuous (U · ω) := Dynkin.continuous_of_integralEq hBc hbc hbM hU
  have hUm : ∀ t, Measurable[𝓕 t] (U t) :=
    Dynkin.measurable_of_integralEq 𝓕 hBad hBc hb hbM hU hUc
  have hUad : Adapted 𝓕 U := hUm
  -- cutoffs
  have hcut : ∀ R : ℕ, ∃ f : E → ℝ, ContDiff ℝ 3 f ∧ (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport f ∧ tsupport f ⊆ O ∧ ∀ x ∈ K ∩ closedBall 0 (R : ℝ), f =ᶠ[𝓝 x] 1 :=
    fun R => exists_cutoff_of_isCompact ((isCompact_closedBall (0 : E) (R : ℝ)).inter_left hK) hO
      (inter_subset_left.trans hKO)
  choose f hfd hfr hfc hfO hf1 using hcut
  set FR : ℕ → E → ℝ := fun R x => f R x * F x with hFR_def
  have hFRd : ∀ R, ContDiff ℝ 3 (FR R) := by
    intro R
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ O
    · exact (hfd R).contDiffAt.mul (hF.contDiffAt (hO.mem_nhds hx))
    · have hx' : x ∉ tsupport (f R) := fun h => hx (hfO R h)
      rw [notMem_tsupport_iff_eventuallyEq] at hx'
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hx'] with y hy
      show f R y * F y = 0
      rw [hy, Pi.zero_apply, zero_mul]
  have hFRc : ∀ R, HasCompactSupport (FR R) := fun R => (hfc R).mul_right
  have hbound : ∀ R, ∃ C, ∀ x, ‖fderiv ℝ (FR R) x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 (FR R) x‖ ≤ C ∧
      ‖iteratedFDeriv ℝ 3 (FR R) x‖ ≤ C := by
    intro R
    obtain ⟨C1, h1⟩ := ((hFRd R).continuous_fderiv (by norm_num)).bounded_above_of_compact_support
      ((hFRc R).fderiv (𝕜 := ℝ))
    obtain ⟨C2, h2⟩ := ((hFRd R).continuous_iteratedFDeriv (m := 2)
      (by norm_num)).bounded_above_of_compact_support ((hFRc R).iteratedFDeriv 2)
    obtain ⟨C3, h3⟩ := ((hFRd R).continuous_iteratedFDeriv (m := 3)
      (by norm_num)).bounded_above_of_compact_support ((hFRc R).iteratedFDeriv 3)
    exact ⟨max C1 (max C2 C3), fun x => ⟨(h1 x).trans (le_max_left _ _),
      (h2 x).trans ((le_max_left _ _).trans (le_max_right _ _)),
      (h3 x).trans ((le_max_right _ _).trans (le_max_right _ _))⟩⟩
  choose C hC using hbound
  have hC0 : ∀ R, 0 ≤ C R := fun R => (norm_nonneg _).trans (hC R 0).1
  have hF0 : ∀ R, ∃ C0, ∀ x, ‖FR R x‖ ≤ C0 := fun R =>
    (hFRd R).continuous.bounded_above_of_compact_support (hFRc R)
  choose C0 hC0' using hF0
  set LR : ℕ → E → ℝ := fun R => dynkinGen b e (FR R) with hLR_def
  have hLRc : ∀ R, Continuous (LR R) := fun R => Dynkin.continuous_dynkinGen (hFRd R) hbc e
  have hLRb : ∀ R x, |LR R x| ≤ C R * Mb + 1 / 2 * (C R * ‖e‖ ^ 2) := by
    intro R x
    simp only [LR, dynkinGen]
    have h1 : |fderiv ℝ (FR R) x (b x)| ≤ C R * Mb := by
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ (FR R) x).le_opNorm (b x)).trans
        (mul_le_mul (hC R x).1 (hbM x) (norm_nonneg _) (hC0 R))
    have h2 : |iteratedFDeriv ℝ 2 (FR R) x ![e, e]| ≤ C R * ‖e‖ ^ 2 :=
      (Dynkin.abs_iteratedFDeriv_two_vec_le _ x e).trans
        (mul_le_mul_of_nonneg_right (hC R x).2.1 (by positivity))
    calc _ ≤ |fderiv ℝ (FR R) x (b x)| + |1 / 2 * iteratedFDeriv ℝ 2 (FR R) x ![e, e]| :=
          abs_add_le _ _
      _ ≤ _ := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          gcongr
  -- generator of the cutoff equals the generator of `F` near `K ∩ closedBall 0 R`
  have hLReq : ∀ (R : ℕ) x, x ∈ K ∩ closedBall 0 (R : ℝ) → LR R x = dynkinGen b e F x := by
    intro R x hx
    have hev : FR R =ᶠ[𝓝 x] F := (hf1 R x hx).mono fun y hy => by
      show f R y * F y = F y
      rw [hy, Pi.one_apply, one_mul]
    simp only [LR, dynkinGen, hev.fderiv_eq, (hev.iteratedFDeriv ℝ 2).eq_of_nhds]
  -- Dynkin martingales, frozen at `T`
  set MR : ℕ → ℝ≥0 → Ω → ℝ := fun R t ω =>
    FR R (U t ω) - FR R u - ∫ r in (0 : ℝ)..t, LR R (U r.toNNReal ω) with hMR_def
  have hMR : ∀ R, Martingale (MR R) 𝓕 P := fun R =>
    Dynkin.dynkin_additive hB hBc 𝓕 hBad hpast hb hbM hU (hFRd R) (hC R)
  have hNR : ∀ R, Martingale (fun t => MR R (min t T)) 𝓕 P := fun R =>
    martingale_min_const (hMR R) T
  have hMRc : ∀ R ω, Continuous fun t => MR R t ω := by
    intro R ω
    have hg : Continuous fun r : ℝ => LR R (U r.toNNReal ω) :=
      (hLRc R).comp ((hUc ω).comp continuous_real_toNNReal)
    have hprim := intervalIntegral.continuous_primitive (μ := volume)
      (fun a b => hg.intervalIntegrable a b) 0
    exact (((hFRd R).continuous.comp (hUc ω)).sub continuous_const).sub
      (hprim.comp NNReal.continuous_coe)
  have hNRc : ∀ R ω, Continuous fun t => MR R (min t T) ω := fun R ω =>
    (hMRc R ω).comp (continuous_id.min continuous_const)
  have hNRb : ∀ R t ω, |MR R (min t T) ω| ≤
      C0 R + C0 R + (C R * Mb + 1 / 2 * (C R * ‖e‖ ^ 2)) * T := by
    intro R t ω
    simp only [MR]
    have h1 := hC0' R (U (min t T) ω)
    have h2 := hC0' R u
    have h3 : ‖∫ r in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), LR R (U r.toNNReal ω)‖ ≤
        (C R * Mb + 1 / 2 * (C R * ‖e‖ ^ 2)) * T := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (fun r _ => by rw [Real.norm_eq_abs]; exact hLRb R _)).trans ?_
      rw [sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)]
      have hK0 : 0 ≤ C R * Mb + 1 / 2 * (C R * ‖e‖ ^ 2) :=
        (abs_nonneg _).trans (hLRb R 0)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right t T) hK0
    rw [Real.norm_eq_abs] at h1 h2 h3
    calc _ ≤ |FR R (U (min t T) ω) - FR R u| + |∫ r in (0 : ℝ)..((min t T : ℝ≥0) : ℝ),
          LR R (U r.toNNReal ω)| := abs_sub _ _
      _ ≤ |FR R (U (min t T) ω)| + |FR R u| + _ := by gcongr; exact abs_sub _ _
      _ ≤ _ := by gcongr
  -- stopping times
  set ClR : ℕ → Set E := fun R => Cl ∪ {x | (R : ℝ) ≤ ‖x‖} with hClR_def
  have hClR : ∀ R, IsClosed (ClR R) := fun R =>
    hCl.union (isClosed_le continuous_const continuous_norm)
  set ρ : ℕ → Ω → ℝ≥0 := fun R ω => hittingBtwn U (ClR R) 0 T ω with hρ_def
  have hρst : ∀ R, IsStoppingTime 𝓕 (fun ω => ((ρ R ω : ℝ≥0) : WithTop ℝ≥0)) := fun R =>
    ItoLite.isStoppingTime_hittingBtwn_of_isClosed hUad hUc (hClR R) T
  have hρT : ∀ R ω, ρ R ω ≤ T := fun R ω => hittingBtwn_le ω
  -- before `ρ R`, the path is in `K`, off `Cl`, and inside the ball
  have hbefore : ∀ R ω (q : ℝ≥0), q < ρ R ω → U q ω ∉ ClR R := fun R ω q hq =>
    notMem_of_lt_hittingBtwn hq zero_le
  have hK_of : ∀ R ω (s : ℝ≥0), s ≤ ρ R ω → U s ω ∈ K := fun R ω s hs =>
    hUK ω s (hs.trans (hρT R ω)) fun q hq h => hbefore R ω q (hq.trans_le hs) (Or.inl h)
  have hLR0 : ∀ R ω (q : ℝ≥0), q < ρ R ω → LR R (U q ω) = 0 := by
    intro R ω q hq
    have hnot := hbefore R ω q hq
    have hball : U q ω ∈ closedBall (0 : E) (R : ℝ) := by
      rw [mem_closedBall_zero_iff]
      exact le_of_lt (not_le.mp fun h => hnot (Or.inr h))
    rw [hLReq R _ ⟨hK_of R ω q hq.le, hball⟩]
    exact hLF _ (hK_of R ω q hq.le) fun h => hnot (Or.inl h)
  have hint0 : ∀ R ω (s : ℝ≥0), s ≤ ρ R ω →
      ∫ r in (0 : ℝ)..(s : ℝ), LR R (U r.toNNReal ω) = 0 := by
    intro R ω s hs
    rw [intervalIntegral.integral_of_le s.coe_nonneg, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero fun r hr => ?_
    have hlt : r.toNNReal < ρ R ω := by
      refine lt_of_lt_of_le ?_ hs
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr.1.le]
      exact hr.2
    exact hLR0 R ω _ hlt
  -- the stopped cutoff processes
  set G : ℕ → ℝ≥0 → Ω → ℝ := fun R t ω => FR R (U (min t (ρ R ω)) ω) with hG_def
  have hGm : ∀ R, Martingale (G R) 𝓕 P := by
    intro R
    have hst := ItoLite.martingale_stopped_of_continuous (hNR R) (hNRc R) (hNRb R) (hρst R)
    have h := hst.add (martingale_const 𝓕 P (FR R u))
    convert h using 1
    funext t ω
    simp only [Pi.add_apply, MR, G]
    rw [min_eq_left ((min_le_right _ _).trans (hρT R ω)),
      hint0 R ω _ (min_le_right _ _)]
    ring
  have hGb : ∀ R t ω, |G R t ω| ≤ M := by
    intro R t ω
    simp only [G, FR]
    rw [abs_mul]
    have hf := hfr R (U (min t (ρ R ω)) ω)
    have hfa : |f R (U (min t (ρ R ω)) ω)| ≤ 1 := by rw [abs_of_nonneg hf.1]; exact hf.2
    calc _ ≤ 1 * |F (U (min t (ρ R ω)) ω)| := by gcongr
      _ ≤ M := by rw [one_mul]; exact hFM _ (hK_of R ω _ (min_le_right _ _))
  -- identification for large `R`
  set τ : Ω → ℝ≥0 := fun ω => hittingBtwn U Cl 0 T ω with hτ_def
  have hlarge : ∀ ω, ∃ R0 : ℕ, ∀ R ≥ R0, ∀ t, G R t ω = F (U (min t (τ ω)) ω) := by
    intro ω
    obtain ⟨Rb, hRb⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
      (hUc ω).continuousOn
    refine ⟨⌈Rb⌉₊ + 1, fun R hR t => ?_⟩
    have hRlt : Rb < R := by
      have h1 : (⌈Rb⌉₊ : ℝ) + 1 ≤ R := by exact_mod_cast hR
      linarith [Nat.le_ceil Rb]
    have hρτ : ρ R ω = τ ω := by
      have hiff : ∀ j ∈ Icc (0 : ℝ≥0) T, (U j ω ∈ ClR R ↔ U j ω ∈ Cl) := by
        intro j hj
        refine ⟨fun h => h.resolve_right fun h' => ?_, Or.inl⟩
        have := hRb j hj
        simp only [mem_setOf_eq] at h'
        linarith
      have hex : (∃ j ∈ Icc (0 : ℝ≥0) T, U j ω ∈ ClR R) ↔ ∃ j ∈ Icc (0 : ℝ≥0) T, U j ω ∈ Cl :=
        ⟨fun ⟨j, hj, h⟩ => ⟨j, hj, (hiff j hj).1 h⟩, fun ⟨j, hj, h⟩ => ⟨j, hj, (hiff j hj).2 h⟩⟩
      have hset : Icc (0 : ℝ≥0) T ∩ {i | U i ω ∈ ClR R} = Icc (0 : ℝ≥0) T ∩ {i | U i ω ∈ Cl} := by
        ext j
        exact ⟨fun ⟨hj, h⟩ => ⟨hj, (hiff j hj).1 h⟩, fun ⟨hj, h⟩ => ⟨hj, (hiff j hj).2 h⟩⟩
      simp only [ρ, τ, hittingBtwn, hset]
      by_cases h : ∃ j ∈ Icc (0 : ℝ≥0) T, U j ω ∈ Cl
      · rw [if_pos h, if_pos (hex.2 h)]
      · rw [if_neg h, if_neg (fun h' => h (hex.1 h'))]
    simp only [G, FR]
    rw [hρτ]
    have hmemK : U (min t (τ ω)) ω ∈ K := by
      have := hK_of R ω (min t (τ ω)) (by rw [hρτ]; exact min_le_right _ _)
      exact this
    have hball : U (min t (τ ω)) ω ∈ closedBall (0 : E) (R : ℝ) := by
      rw [mem_closedBall_zero_iff]
      have hτT : τ ω ≤ T := hittingBtwn_le ω
      exact (hRb _ ⟨zero_le, (min_le_right _ _).trans hτT⟩).trans hRlt.le
    rw [(hf1 R _ ⟨hmemK, hball⟩).self_of_nhds, Pi.one_apply, one_mul]
  have htend : ∀ t ω, Tendsto (fun R => G R t ω) atTop (𝓝 (F (U (min t (τ ω)) ω))) := by
    intro t ω
    obtain ⟨R0, hR0⟩ := hlarge ω
    exact tendsto_const_nhds.congr' (eventually_atTop.2 ⟨R0, fun R hR => (hR0 R hR t).symm⟩)
  -- the limit is a martingale
  have hgm : ∀ t, StronglyMeasurable[𝓕 t] (fun ω => F (U (min t (τ ω)) ω)) := fun t =>
    stronglyMeasurable_of_tendsto atTop (fun R => (hGm R).stronglyAdapted t)
      (tendsto_pi_nhds.2 (htend t))
  have hgb : ∀ t ω, |F (U (min t (τ ω)) ω)| ≤ M := fun t ω =>
    le_of_tendsto' ((continuous_abs.tendsto _).comp (htend t ω)) fun R => hGb R t ω
  have hgi : ∀ t, Integrable (fun ω => F (U (min t (τ ω)) ω)) P := fun t =>
    ItoLite.integrable_of_bound_abs ((hgm t).mono (𝓕.le t)) (hgb t)
  refine ItoLite.martingale_of_setIntegral_eq_nnreal hgm hgi fun s t hst A hA => ?_
  have hDCT : ∀ t', Tendsto (fun R => ∫ ω in A, G R t' ω ∂P) atTop
      (𝓝 (∫ ω in A, F (U (min t' (τ ω)) ω) ∂P)) := by
    intro t'
    refine tendsto_integral_of_dominated_convergence (fun _ => M)
      (fun R => (((hGm R).stronglyAdapted t').mono (𝓕.le t')).aestronglyMeasurable)
      (integrable_const M) (fun R => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => htend t' ω)
    rw [Real.norm_eq_abs]; exact hGb R t' ω
  have h1 := hDCT s
  have h2 := hDCT t
  have heq : (fun R => ∫ ω in A, G R s ω ∂P) = fun R => ∫ ω in A, G R t ω ∂P :=
    funext fun R => (hGm R).setIntegral_eq hst hA
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

end LocalDynkin

end FrozenMart
end QuantumZipper
