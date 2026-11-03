/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovGermVer3B at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer3A

/-!
# Germ step for unbounded `V`: reduction to a uniform truncation bound (task P2-MKD3)

`mem_range_cmIso_of_orth_trunc`: the germ step for an arbitrary open `V` follows from the
bounded case (`mem_range_cmIso_of_orth`) once there are cutoffs `λₙ ∈ C_c^∞(ℂ)`, `λₙ = 1` on
`B̄(0,n)`, with `∫‖∇λₙ‖² → 0`, and a probability density `ρ ∈ C_c^∞` supported in
`O = B_ε(ℂ∖V)` such that the truncations `Tₙ g = λₙ (g − ∫ gρ)` are **uniformly** bounded for
the Dirichlet energy (`gradEnergy (Tₙ g) ≤ M gradEnergy g`).

Proof. Let `w = cmIso ⊤ v ⊥ S(O)` and `(h, f_k)_∇ → w`. `(h, Tₙ f_k)_∇` is Cauchy; its limit
`zₙ` is orthogonal to `S(B_ε((V ∩ B(0,Rₙ+2ε))ᶜ))` because
`⟪(h, Tₙ g)_∇, ⟨h,ψ⟩⟫ = ⟪(h, g)_∇, ⟨h, λₙψ − (∫λₙψ) ρ⟩⟫` and `λₙψ − (∫λₙψ)ρ` is a mean-zero test
function supported in `O`. The bounded case puts `zₙ` in the range of `cmIso (V ∩ B)` ⊆ range of
`cmIso V`, and `‖w − zₙ‖ ≤ (1 + √M)‖w − (h,f)_∇‖ + |∫fρ| ‖(h, λₙ)_∇‖` (for `n` past `supp f`).

This is the standard truncation argument for "`C_c^∞(V)` is dense in the Dirichlet space of `V`
modulo constants in 2D" (logarithmic cutoffs: Berestycki–Powell arXiv:2404.16642 §1.8); the
Hilbert-space bookkeeping is our own.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovGermVer

open MarkovGauss MarkovZB MarkovGerm MarkovExt MarkovNorm Blueprint QuantumZipper
  QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- the range of `cmIso` is monotone in the domain -/
lemma cmIso_mem_range_of_le (hh : IsWholePlaneGFF h P) {U V : Opens ℂ} (hUV : U ≤ V)
    (v : gradClosure (U : Set ℂ) (zeroSpace (U : Set ℂ))) :
    cmIso hh U v ∈ Set.range (cmIso hh V) := by
  have hcl : IsClosed (Set.range (cmIso hh V)) :=
    (cmIso hh V).isometry.isClosedEmbedding.isClosed_range
  refine (denseRange_gradLin U).induction_on v (hcl.preimage (cmIso hh U).continuous)
    fun f => ?_
  have hf : f.1 ∈ zeroSpace (V : Set ℂ) := ⟨f.2.1, f.2.2.1, f.2.2.2.trans hUV⟩
  refine ⟨gradLin V ⟨f.1, hf⟩, ?_⟩
  rw [cmIso_gradLin, cmIso_gradLin]; rfl

lemma thickening_compl_inter_ball_subset {V : Set ℂ} {ε R : ℝ} :
    thickening ε (V ∩ ball 0 (R + 2 * ε))ᶜ ⊆ thickening ε Vᶜ ∪ {x | R + ε < ‖x‖} := by
  rw [compl_inter, thickening_union]
  refine union_subset_union_right _ fun x hx => ?_
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hx
  have hy' : R + 2 * ε ≤ ‖y‖ := by simpa [mem_ball, dist_zero_right, not_lt] using hy
  have := norm_sub_norm_le y x
  rw [dist_eq_norm] at hxy
  rw [norm_sub_rev] at hxy
  show R + ε < ‖x‖
  linarith

lemma integrable_mul_of_zs {g ρ : ℂ → ℝ} (hg : Continuous g) (hρ : Continuous ρ)
    (hρc : HasCompactSupport ρ) : Integrable fun y => g y * ρ y :=
  (hg.mul hρ).integrable_of_hasCompactSupport hρc.mul_left

set_option maxHeartbeats 1000000 in
/-- **The germ step from a uniform truncation bound** (any open `V`). -/
theorem mem_range_cmIso_of_orth_trunc (hh : IsNormalizedWPGFF h P) {V : Opens ℂ} {ε : ℝ}
    (hε : 0 < ε)
    (v : gradClosure ((⊤ : Opens ℂ) : Set ℂ) (zeroSpace ((⊤ : Opens ℂ) : Set ℂ)))
    (hv : ∀ u ∈ germSpan hh.1 (nbhdO ε (V : Set ℂ)ᶜ), ⟪u, cmIso hh.1 ⊤ v⟫ = 0)
    {ρ : ℂ → ℝ} (hρs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (hρO : tsupport ρ ⊆ (nbhdO ε (V : Set ℂ)ᶜ : Set ℂ)) (hρ1 : ∫ x, ρ x = 1)
    {lam : ℕ → ℂ → ℝ} (hlam : ∀ n, lam n ∈ zeroSpace ((⊤ : Opens ℂ) : Set ℂ))
    (hlam1 : ∀ (n : ℕ) (x : ℂ), ‖x‖ ≤ (n : ℝ) → lam n x = 1)
    (hlamE : Tendsto (fun n => gradEnergy (lam n)) atTop (𝓝 0))
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ n, ∀ g ∈ zeroSpace ((⊤ : Opens ℂ) : Set ℂ),
      gradEnergy (fun x => lam n x * (g x - ∫ y, g y * ρ y)) ≤ M * gradEnergy g) :
    cmIso hh.1 ⊤ v ∈ Set.range (cmIso hh.1 V) := by
  set w := cmIso hh.1 ⊤ v with hwdef
  set O : Set ℂ := (nbhdO ε (V : Set ℂ)ᶜ : Set ℂ) with hO
  have hgc : ∀ g : zsSub ((⊤ : Opens ℂ) : Set ℂ), Continuous g.1 := fun g => g.2.1.continuous
  set c : (ℂ → ℝ) → ℝ := fun g => ∫ y, g y * ρ y with hc
  have memT : ∀ n (g : zsSub ((⊤ : Opens ℂ) : Set ℂ)),
      (fun x => lam n x * (g.1 x - c g.1)) ∈ zeroSpace ((⊤ : Opens ℂ) : Set ℂ) :=
    fun n g => ⟨(hlam n).1.mul (g.2.1.sub contDiff_const), (hlam n).2.1.mul_right, subset_univ _⟩
  set T : ℕ → zsSub ((⊤ : Opens ℂ) : Set ℂ) → zsSub ((⊤ : Opens ℂ) : Set ℂ) :=
    fun n g => ⟨_, memT n g⟩ with hT
  set A : ℕ → zsSub ((⊤ : Opens ℂ) : Set ℂ) → Lp ℝ 2 P := fun n g => cmLin hh.1 ⊤ (T n g)
    with hA
  have hcsub : ∀ g g' : zsSub ((⊤ : Opens ℂ) : Set ℂ), c (g - g').1 = c g.1 - c g'.1 := by
    intro g g'
    simp only [c, Submodule.coe_sub, Pi.sub_apply, sub_mul]
    exact integral_sub (integrable_mul_of_zs (hgc g) hρs.continuous hρc)
      (integrable_mul_of_zs (hgc g') hρs.continuous hρc)
  have hAsub : ∀ n g g', A n (g - g') = A n g - A n g' := by
    intro n g g'
    have hTs : T n (g - g') = T n g - T n g' := by
      refine Subtype.ext (funext fun x => ?_)
      simp only [T, Submodule.coe_sub, Pi.sub_apply]
      rw [show c (g.1 - g'.1) = c g.1 - c g'.1 from hcsub g g']
      ring
    simp only [A]
    rw [hTs, map_sub]
  have hAb : ∀ n g, ‖A n g‖ ≤ Real.sqrt M * ‖cmLin hh.1 ⊤ g‖ := by
    intro n g
    have h2 : ‖A n g‖ ^ 2 ≤ M * ‖cmLin hh.1 ⊤ g‖ ^ 2 := by
      simp only [A]
      rw [norm_cmLin_sq, norm_cmLin_sq]
      exact hM n g.1 g.2
    have := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hM0, Real.sqrt_sq (norm_nonneg _)] at this
  -- approximating sequence
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (denseRange_gradLin (⊤ : Opens ℂ) v)
  choose f hf using hu
  set W : ℕ → Lp ℝ 2 P := fun k => cmLin hh.1 ⊤ (f k) with hWdef
  have hW : Tendsto W atTop (𝓝 w) := by
    have := ((cmIso hh.1 ⊤).continuous.tendsto v).comp hlim
    refine this.congr fun k => ?_
    simp only [Function.comp, W, ← hf k, cmIso_gradLin]
  have hAW : ∀ n k k', ‖A n (f k) - A n (f k')‖ ≤ Real.sqrt M * ‖W k - W k'‖ := by
    intro n k k'
    rw [← hAsub]
    refine (hAb n _).trans_eq ?_
    simp only [W, map_sub]
  have hcau : ∀ n, CauchySeq fun k => A n (f k) := by
    intro n
    rw [Metric.cauchySeq_iff]
    intro δ hδ
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hW.cauchySeq (δ / (Real.sqrt M + 1))
      (by positivity)
    refine ⟨N, fun a ha b hb => ?_⟩
    have h1 := hN a ha b hb
    rw [dist_eq_norm] at h1 ⊢
    have hs := Real.sqrt_nonneg M
    calc ‖A n (f a) - A n (f b)‖ ≤ Real.sqrt M * ‖W a - W b‖ := hAW n a b
      _ ≤ (Real.sqrt M + 1) * ‖W a - W b‖ := by nlinarith [norm_nonneg (W a - W b)]
      _ < (Real.sqrt M + 1) * (δ / (Real.sqrt M + 1)) := by
          exact mul_lt_mul_of_pos_left h1 (by positivity)
      _ = δ := by field_simp
  choose z hz using fun n => cauchySeq_tendsto_of_complete (hcau n)
  have hclT : IsClosed (Set.range (cmIso hh.1 ⊤)) :=
    (cmIso hh.1 ⊤).isometry.isClosedEmbedding.isClosed_range
  have Z1 : ∀ n, z n ∈ Set.range (cmIso hh.1 ⊤) := fun n =>
    hclT.mem_of_tendsto (hz n) (Eventually.of_forall fun k =>
      ⟨gradLin ⊤ (T n (f k)), cmIso_gradLin _ _ _⟩)
  -- the bounded domains
  choose R hR using fun n => (hlam n).2.1.isCompact.isBounded.subset_closedBall (0 : ℂ)
  set U : ℕ → Opens ℂ := fun n => V ⊓ ⟨ball 0 (R n + 2 * ε), isOpen_ball⟩ with hU
  have hUc : ∀ n, ((U n : Set ℂ)) = (V : Set ℂ) ∩ ball 0 (R n + 2 * ε) := fun n => rfl
  -- the adjoint identity
  have hadj : ∀ n (ψ : TestC0), tsupport (ψ.1 : ℂ → ℝ) ⊆ (nbhdO ε (U n : Set ℂ)ᶜ : Set ℂ) →
      ∃ p : TestC0, tsupport (p.1 : ℂ → ℝ) ⊆ O ∧ ∀ g : zsSub ((⊤ : Opens ℂ) : Set ℂ),
        ⟪A n g, (memLp_pair hh.1 ψ).toLp (pairProc h ψ)⟫ =
          ⟪cmLin hh.1 ⊤ g, (memLp_pair hh.1 p).toLp (pairProc h p)⟫ := by
    intro n ψ hψ
    have hψs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ.1 : ℂ → ℝ) := ψ.1.contDiff
    have hψc : HasCompactSupport (ψ.1 : ℂ → ℝ) := ψ.1.hasCompactSupport
    set a := ∫ y, lam n y * ψ.1 y
    set pf : ℂ → ℝ := fun x => lam n x * ψ.1 x - a * ρ x with hpf
    have hls : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lam n) := (hlam n).1
    have hlψc : HasCompactSupport fun x => lam n x * ψ.1 x := (hlam n).2.1.mul_right
    have haρc : HasCompactSupport fun x => a * ρ x := hcs_of_vanish hρc fun x hx => by simp [hx]
    have hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) pf := (hls.mul hψs).sub (contDiff_const.mul hρs)
    have hpc : HasCompactSupport pf := hlψc.sub haρc
    have hlψi : Integrable fun x => lam n x * ψ.1 x :=
      (hls.continuous.mul hψs.continuous).integrable_of_hasCompactSupport hlψc
    have hρi : Integrable ρ := hρs.continuous.integrable_of_hasCompactSupport hρc
    have hp0 : ∫ x, pf x = 0 := by
      simp only [pf]
      rw [integral_sub hlψi (hρi.const_mul a), integral_const_mul, hρ1, mul_one, sub_self]
    refine ⟨⟨tC hps hpc, hp0⟩, ?_, fun g => ?_⟩
    · change tsupport pf ⊆ O
      have h1 : tsupport (fun x => lam n x * ψ.1 x) ⊆ O := by
        intro x hx
        have hx1 := hR n (tsupport_mul_subset_left hx)
        have hx2 := thickening_compl_inter_ball_subset (hψ (tsupport_mul_subset_right hx))
        rcases hx2 with hx2 | hx2
        · exact hx2
        · exfalso
          have := mem_closedBall_zero_iff.1 hx1
          change R n + ε < ‖x‖ at hx2
          linarith
      have h2 : tsupport (fun x => a * ρ x) ⊆ O := (tsupport_mul_subset_right).trans hρO
      refine (closure_minimal (fun x hx => ?_) ((isClosed_tsupport _).union
        (isClosed_tsupport _))).trans (union_subset h1 h2)
      by_contra hn
      simp only [mem_union, not_or] at hn
      apply hx
      simp only [pf, image_eq_zero_of_notMem_tsupport hn.1, image_eq_zero_of_notMem_tsupport hn.2,
        sub_zero]
    · refine (inner_cmLin_pair hh.1 ⊤ (T n g) ψ).trans
        ((?_ : _ = _).trans (inner_cmLin_pair hh.1 ⊤ g _).symm)
      change ∫ x, (ψ.1 : ℂ → ℝ) x * (lam n x * (g.1 x - c g.1)) = ∫ x, pf x * g.1 x
      have hgi : Integrable fun x => lam n x * ψ.1 x * g.1 x :=
        ((hls.continuous.mul hψs.continuous).mul (hgc g)).integrable_of_hasCompactSupport
          hlψc.mul_right
      have hgρ : Integrable fun x => g.1 x * ρ x := integrable_mul_of_zs (hgc g) hρs.continuous hρc
      have e1 : (fun x => ψ.1 x * (lam n x * (g.1 x - c g.1))) =
          fun x => lam n x * ψ.1 x * g.1 x - c g.1 * (lam n x * ψ.1 x) := funext fun x => by ring
      have e2 : (fun x => pf x * g.1 x) =
          fun x => lam n x * ψ.1 x * g.1 x - a * (g.1 x * ρ x) := funext fun x => by
        simp only [pf]; ring
      rw [e1, e2, integral_sub hgi (hlψi.const_mul _), integral_sub hgi (hgρ.const_mul _),
        integral_const_mul, integral_const_mul]
      simp only [c, a]; ring
  -- orthogonality of the limits
  have Z2 : ∀ n (ψ : TestC0), tsupport (ψ.1 : ℂ → ℝ) ⊆ (nbhdO ε (U n : Set ℂ)ᶜ : Set ℂ) →
      ⟪z n, (memLp_pair hh.1 ψ).toLp (pairProc h ψ)⟫ = 0 := by
    intro n ψ hψ
    obtain ⟨p, hpO, hp⟩ := hadj n ψ hψ
    have h1 : Tendsto (fun k => ⟪A n (f k), (memLp_pair hh.1 ψ).toLp (pairProc h ψ)⟫) atTop
        (𝓝 ⟪z n, (memLp_pair hh.1 ψ).toLp (pairProc h ψ)⟫) := (hz n).inner tendsto_const_nhds
    have h2 : Tendsto (fun k => ⟪W k, (memLp_pair hh.1 p).toLp (pairProc h p)⟫) atTop
        (𝓝 ⟪w, (memLp_pair hh.1 p).toLp (pairProc h p)⟫) := hW.inner tendsto_const_nhds
    have h1' : Tendsto (fun k => ⟪W k, (memLp_pair hh.1 p).toLp (pairProc h p)⟫) atTop
        (𝓝 ⟪z n, (memLp_pair hh.1 ψ).toLp (pairProc h ψ)⟫) :=
      h1.congr fun k => hp (f k)
    rw [tendsto_nhds_unique h1' h2, real_inner_comm]
    exact hv _ (toLp_mem_germSpan hh.1 p hpO)
  have Z3 : ∀ n, ∀ u ∈ germSpan hh.1 (nbhdO ε (U n : Set ℂ)ᶜ), ⟪u, z n⟫ = 0 := by
    intro n u hu
    have hle : germSpan hh.1 (nbhdO ε (U n : Set ℂ)ᶜ) ≤ (ℝ ∙ z n)ᗮ := by
      refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
        (Submodule.isClosed_orthogonal _)
      rintro _ ⟨ψ, hψ, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact Z2 n ψ hψ
    have := hle hu
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
    rw [real_inner_comm]; exact this
  have Z4 : ∀ n, z n ∈ Set.range (cmIso hh.1 V) := by
    intro n
    obtain ⟨vn, hvn⟩ := Z1 n
    have hUb : Bornology.IsBounded (U n : Set ℂ) := by
      rw [hUc]; exact isBounded_ball.subset inter_subset_right
    obtain ⟨y, hy⟩ := mem_range_cmIso_of_orth hh hUb hε vn (by rw [hvn]; exact Z3 n)
    rw [← hvn, ← hy]
    exact cmIso_mem_range_of_le hh.1 inf_le_left y
  -- distance estimates
  have Z5 : ∀ n k₀, ‖A n (f k₀) - z n‖ ≤ Real.sqrt M * ‖W k₀ - w‖ := by
    intro n k₀
    have hl : Tendsto (fun k => ‖A n (f k₀) - A n (f k)‖) atTop (𝓝 ‖A n (f k₀) - z n‖) :=
      (tendsto_const_nhds.sub (hz n)).norm
    have hr : Tendsto (fun k => Real.sqrt M * ‖W k₀ - W k‖) atTop
        (𝓝 (Real.sqrt M * ‖W k₀ - w‖)) :=
      ((tendsto_const_nhds.sub hW).norm).const_mul _
    exact le_of_tendsto_of_tendsto' hl hr fun k => hAW n k₀ k
  have Z6 : ∀ k₀, ∃ R₀ : ℝ, ∀ n : ℕ, R₀ ≤ n →
      ‖W k₀ - A n (f k₀)‖ ^ 2 = c (f k₀).1 ^ 2 * gradEnergy (lam n) := by
    intro k₀
    obtain ⟨R₀, hR₀⟩ := (f k₀).2.2.1.isCompact.isBounded.subset_closedBall (0 : ℂ)
    refine ⟨R₀, fun n hn => ?_⟩
    have he : f k₀ - T n (f k₀) = c (f k₀).1 • (⟨lam n, hlam n⟩ : zsSub _) := by
      refine Subtype.ext (funext fun x => ?_)
      simp only [T, Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      by_cases hx : ‖x‖ ≤ n
      · rw [hlam1 n x hx]; ring
      · have hx0 : (f k₀).1 x = 0 := image_eq_zero_of_notMem_tsupport fun hx' => hx
          ((mem_closedBall_zero_iff.1 (hR₀ hx')).trans hn)
        rw [hx0]; ring
    simp only [W, A]
    rw [← map_sub, he, map_smul, norm_smul, mul_pow, norm_cmLin_sq, Real.norm_eq_abs, sq_abs]
  -- conclusion
  have hcl : IsClosed (Set.range (cmIso hh.1 V)) :=
    (cmIso hh.1 V).isometry.isClosedEmbedding.isClosed_range
  rw [← hcl.closure_eq, Metric.mem_closure_iff]
  intro δ hδ
  set s := Real.sqrt M
  have hs := Real.sqrt_nonneg M
  obtain ⟨k₀, hk₀⟩ := Metric.tendsto_atTop.1 hW (δ / (3 * (s + 1))) (by positivity)
  have he0 : ‖W k₀ - w‖ < δ / (3 * (s + 1)) := by
    have := hk₀ k₀ le_rfl; rwa [dist_eq_norm] at this
  obtain ⟨R₀, hR₀⟩ := Z6 k₀
  have hlim2 : Tendsto (fun n => c (f k₀).1 ^ 2 * gradEnergy (lam n)) atTop (𝓝 0) := by
    simpa using hlamE.const_mul (c (f k₀).1 ^ 2)
  obtain ⟨n, hn1, hn2⟩ := ((hlim2.eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < (δ / 3) ^ 2))).and (tendsto_natCast_atTop_atTop.eventually_ge_atTop R₀)).exists
  have h3 : ‖W k₀ - A n (f k₀)‖ < δ / 3 := by
    have h4 : ‖W k₀ - A n (f k₀)‖ ^ 2 < (δ / 3) ^ 2 := by rw [hR₀ n hn2]; exact hn1
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h4
  refine ⟨z n, Z4 n, ?_⟩
  rw [dist_eq_norm]
  have htri : ‖w - z n‖ ≤ ‖w - W k₀‖ + ‖W k₀ - A n (f k₀)‖ + ‖A n (f k₀) - z n‖ := by
    have e : w - z n = (w - W k₀) + (W k₀ - A n (f k₀)) + (A n (f k₀) - z n) := by abel
    rw [e]; exact norm_add₃_le
  have h5 := Z5 n k₀
  rw [norm_sub_rev w (W k₀)] at htri
  have hs1 : s + 1 ≠ 0 := by positivity
  have h6 : (s + 1) * ‖W k₀ - w‖ < δ / 3 := by
    calc (s + 1) * ‖W k₀ - w‖ < (s + 1) * (δ / (3 * (s + 1))) :=
          mul_lt_mul_of_pos_left he0 (by positivity)
      _ = δ / 3 := by field_simp
  nlinarith

end MarkovGermVer
end LQGMetric
