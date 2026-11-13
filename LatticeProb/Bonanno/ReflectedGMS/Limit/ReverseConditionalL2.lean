/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ReverseConditionalL2 at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
Reverse (decreasing sigma-field) L² convergence of conditional expectations.

Temporal homogenization averages time blocks against a *decreasing* family of
sigma-fields, so the Lévy upward theorem available in mathlib
(`MeasureTheory.Integrable.tendsto_eLpNorm_condExp`) is not applicable. Mathlib
has no antitone counterpart, so the two genuinely new ingredients proved here are

* `cauchySeq_starProjection_of_antitone`: orthogonal projections onto an antitone
  family of subspaces of a real inner-product space form a Cauchy sequence. The
  proof is the monotone-squared-distance argument: the Pythagoras identity
  `‖x - v‖² = ‖x - Px‖² + ‖Px - v‖²` for `v` in the subspace shows the squared
  distances increase, stay bounded by `‖x‖²`, and control the projection gaps.
* `aestronglyMeasurable_iInf_of_antitone`: a function almost everywhere equal to
  an `m n`-strongly measurable function for every `n` is almost everywhere equal
  to a `⨅ n, m n`-measurable function. The tail representative is the pointwise
  `limsup` of the chosen versions, which is `m n`-measurable for every `n`
  because `limsup` ignores the first `n` terms; measurability for the infimum
  sigma-algebra is then the intersection description `measurableSet_iInf`. This
  is what makes the limit subspace the honest `lpMeas` of the intersection, not
  an assumed intersection of a.e.-measurable subspaces.

These combine into `tendsto_eLpNorm_condExp_iInf`, the L² convergence
`E[f | m n] → E[f | ⨅ k, m k]`. Conditional expectations are mathlib's
`MeasureTheory.condExp`/`condExpL2`; nothing about them is reimplemented, and the
tail limit is identified by the orthogonal-projection characterization rather
than with an unconditional mean.
-/
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal NNReal Topology InnerProductSpace

namespace ReflectedGMS.MartingaleLimit

section Projection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Pythagoras relative to an orthogonal projection: the distance to a point of the
subspace splits into the projection distance and the in-subspace distance. -/
theorem norm_sub_sq_starProjection (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (x : H) {v : H} (hv : v ∈ K) :
    ‖x - v‖ ^ 2 = ‖x - K.starProjection x‖ ^ 2 + ‖K.starProjection x - v‖ ^ 2 := by
  have hmem : K.starProjection x - v ∈ K := K.sub_mem (K.starProjection_apply_mem x) hv
  have hinner : ⟪x - K.starProjection x, K.starProjection x - v⟫_ℝ = 0 :=
    Submodule.starProjection_inner_eq_zero x _ hmem
  have hsplit : x - v = (x - K.starProjection x) + (K.starProjection x - v) := by abel
  rw [hsplit, norm_add_sq_real, hinner]
  ring

/-- Orthogonal projections onto an antitone sequence of subspaces form a Cauchy
sequence: the squared distances to the subspaces increase and are bounded by `‖x‖²`,
and their increments are exactly the squared projection gaps. -/
theorem cauchySeq_starProjection_of_antitone (K : ℕ → Submodule ℝ H)
    [∀ n, (K n).HasOrthogonalProjection] (hK : Antitone K) (x : H) :
    CauchySeq fun n => (K n).starProjection x := by
  have key : ∀ n k, n ≤ k →
      ‖x - (K k).starProjection x‖ ^ 2 =
        ‖x - (K n).starProjection x‖ ^ 2 +
          ‖(K n).starProjection x - (K k).starProjection x‖ ^ 2 := fun n k hnk =>
    norm_sub_sq_starProjection (K n) x (hK hnk ((K k).starProjection_apply_mem x))
  have hmono : Monotone fun n => ‖x - (K n).starProjection x‖ ^ 2 := by
    intro n k hnk
    simp only
    rw [key n k hnk]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hbdd : BddAbove (Set.range fun n => ‖x - (K n).starProjection x‖ ^ 2) := by
    refine ⟨‖x‖ ^ 2, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h0 := norm_sub_sq_starProjection (K n) x (K n).zero_mem
    rw [sub_zero] at h0
    nlinarith [sq_nonneg ‖(K n).starProjection x - 0‖]
  have hcauchy : CauchySeq fun n => ‖x - (K n).starProjection x‖ ^ 2 :=
    (tendsto_atTop_ciSup hmono hbdd).cauchySeq
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hcauchy (ε ^ 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hdist := hN n hn
  rw [Real.dist_eq] at hdist
  have hlt : ‖x - (K n).starProjection x‖ ^ 2 - ‖x - (K N).starProjection x‖ ^ 2 < ε ^ 2 :=
    lt_of_le_of_lt (le_abs_self _) hdist
  have hgap : ‖(K N).starProjection x - (K n).starProjection x‖ ^ 2 < ε ^ 2 := by
    rw [key N n hn] at hlt
    linarith
  rw [dist_eq_norm']
  nlinarith [norm_nonneg ((K N).starProjection x - (K n).starProjection x)]

end Projection

section TailMeasurable

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Tail measurability for an antitone sequence of sigma-algebras: a function that is
a.e. equal to an `m n`-strongly measurable function for every `n` is a.e. equal to a
`⨅ n, m n`-strongly measurable function. The tail representative is the pointwise
`limsup` of the chosen versions. -/
theorem aestronglyMeasurable_iInf_of_antitone {m : ℕ → MeasurableSpace Ω}
    (hmono : Antitone m) {g : Ω → ℝ} (hg : ∀ n, AEStronglyMeasurable[m n] g μ) :
    AEStronglyMeasurable[⨅ n, m n] g μ := by
  classical
  obtain ⟨u, hu_meas, hu_ae⟩ : ∃ u : ℕ → Ω → ℝ,
      (∀ k, StronglyMeasurable[m k] (u k)) ∧ ∀ k, g =ᵐ[μ] u k :=
    ⟨fun k => (hg k).mk g, fun k => (hg k).stronglyMeasurable_mk, fun k => (hg k).ae_eq_mk⟩
  have hmeas_n : ∀ n, Measurable[m n] fun ω => limsup (fun k => u k ω) atTop := by
    intro n
    have hshift : (fun ω => limsup (fun k => u k ω) atTop) =
        fun ω => limsup (fun i => u (i + n) ω) atTop := by
      funext ω
      exact (limsup_nat_add (fun k => u k ω) n).symm
    rw [hshift]
    exact Measurable.limsup fun i =>
      ((hu_meas (i + n)).mono (hmono (Nat.le_add_left n i))).measurable
  have hmeas : Measurable[⨅ n, m n] fun ω => limsup (fun k => u k ω) atTop :=
    fun _ ht => MeasurableSpace.measurableSet_iInf.2 fun n => hmeas_n n ht
  refine ⟨fun ω => limsup (fun k => u k ω) atTop, hmeas.stronglyMeasurable, ?_⟩
  filter_upwards [ae_all_iff.2 hu_ae] with ω hω
  have hconst : (fun k => u k ω) = fun _ => g ω := funext fun k => (hω k).symm
  rw [hconst, limsup_const]

end TailMeasurable

/-- Monotonicity of `lpMeas` in the sigma-algebra. The ambient sigma-algebra `m0` is
declared last so that it is the local instance used by `μ` and `Lp`. -/
theorem lpMeas_mono {Ω : Type*} {m₁ m₂ m0 : MeasurableSpace Ω} {μ : Measure Ω}
    (h : m₁ ≤ m₂) (x : Lp ℝ 2 μ) (hx : x ∈ lpMeas ℝ ℝ m₁ 2 μ) :
    x ∈ lpMeas ℝ ℝ m₂ 2 μ := by
  rw [mem_lpMeas_iff_aestronglyMeasurable] at hx ⊢
  exact ⟨hx.mk _, hx.stronglyMeasurable_mk.mono h, hx.ae_eq_mk⟩

section Reverse

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

/-- **Reverse L² convergence of conditional expectations.** For a finite measure, an
antitone sequence of sub-sigma-algebras and `f ∈ L²`, the conditional expectations
`E[f | m n]` converge in `L²` to `E[f | ⨅ k, m k]`. -/
theorem tendsto_eLpNorm_condExp_iInf {m : ℕ → MeasurableSpace Ω} (hm : ∀ n, m n ≤ m0)
    (hmono : Antitone m) {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    Tendsto (fun n => eLpNorm (μ[f|m n] - μ[f|⨅ k, m k]) 2 μ) atTop (𝓝 0) := by
  have hfact : ∀ n, Fact (m n ≤ m0) := fun n => ⟨hm n⟩
  have hmInf : (⨅ k, m k) ≤ m0 := le_trans (iInf_le m 0) (hm 0)
  have hfactInf : Fact ((⨅ k, m k) ≤ m0) := ⟨hmInf⟩
  have hKanti : Antitone fun n => lpMeas ℝ ℝ (m n) 2 μ := by
    intro a b hab
    rw [SetLike.le_def]
    exact fun x hx => lpMeas_mono (hmono hab) x hx
  obtain ⟨G, hG⟩ :=
    cauchySeq_tendsto_of_complete
      (cauchySeq_starProjection_of_antitone (fun n => lpMeas ℝ ℝ (m n) 2 μ) hKanti (hf.toLp f))
  -- `G` lies in every `lpMeas ℝ ℝ (m n) 2 μ`, being a limit of elements of the tail.
  have hGmem : ∀ n, G ∈ lpMeas ℝ ℝ (m n) 2 μ := by
    intro n
    have h1 : Tendsto
        (fun k => (lpMeas ℝ ℝ (m n) 2 μ).starProjection
          ((lpMeas ℝ ℝ (m k) 2 μ).starProjection (hf.toLp f))) atTop
        (𝓝 ((lpMeas ℝ ℝ (m n) 2 μ).starProjection G)) :=
      ((lpMeas ℝ ℝ (m n) 2 μ).starProjection.continuous.tendsto G).comp hG
    have h2 : Tendsto
        (fun k => (lpMeas ℝ ℝ (m n) 2 μ).starProjection
          ((lpMeas ℝ ℝ (m k) 2 μ).starProjection (hf.toLp f))) atTop (𝓝 G) := by
      refine hG.congr' ?_
      filter_upwards [eventually_ge_atTop n] with k hk
      exact (Submodule.starProjection_eq_self_iff.2
        (hKanti hk ((lpMeas ℝ ℝ (m k) 2 μ).starProjection_apply_mem (hf.toLp f)))).symm
    exact Submodule.starProjection_eq_self_iff.1 (tendsto_nhds_unique h1 h2)
  -- Tail measurability identifies the limit subspace with `lpMeas` of the intersection.
  have hGinf : G ∈ lpMeas ℝ ℝ (⨅ k, m k) 2 μ := by
    rw [mem_lpMeas_iff_aestronglyMeasurable]
    exact aestronglyMeasurable_iInf_of_antitone hmono fun n =>
      mem_lpMeas_iff_aestronglyMeasurable.1 (hGmem n)
  have hGproj : (lpMeas ℝ ℝ (⨅ k, m k) 2 μ).starProjection (hf.toLp f) = G := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hGinf ?_
    intro w hw
    have hzero : ∀ n,
        ⟪hf.toLp f - (lpMeas ℝ ℝ (m n) 2 μ).starProjection (hf.toLp f), w⟫_ℝ = 0 := fun n =>
      Submodule.starProjection_inner_eq_zero _ _ (lpMeas_mono (iInf_le m n) w hw)
    have htend : Tendsto
        (fun n => ⟪hf.toLp f - (lpMeas ℝ ℝ (m n) 2 μ).starProjection (hf.toLp f), w⟫_ℝ) atTop
        (𝓝 ⟪hf.toLp f - G, w⟫_ℝ) := (tendsto_const_nhds.sub hG).inner tendsto_const_nhds
    refine tendsto_nhds_unique htend ?_
    simp only [hzero]
    exact tendsto_const_nhds
  -- Identify the projections with mathlib's conditional expectations.
  have hae : ∀ n,
      ((((lpMeas ℝ ℝ (m n) 2 μ).starProjection (hf.toLp f) : Lp ℝ 2 μ) : Ω → ℝ))
        =ᵐ[μ] μ[f|m n] := fun n => hf.condExpL2_ae_eq_condExp (𝕜 := ℝ) (hm n)
  have haeInf :
      ((((lpMeas ℝ ℝ (⨅ k, m k) 2 μ).starProjection (hf.toLp f) : Lp ℝ 2 μ) : Ω → ℝ))
        =ᵐ[μ] μ[f|⨅ k, m k] := hf.condExpL2_ae_eq_condExp (𝕜 := ℝ) hmInf
  have heq : ∀ n, eLpNorm (μ[f|m n] - μ[f|⨅ k, m k]) 2 μ =
      ENNReal.ofReal ‖(lpMeas ℝ ℝ (m n) 2 μ).starProjection (hf.toLp f) -
        (lpMeas ℝ ℝ (⨅ k, m k) 2 μ).starProjection (hf.toLp f)‖ := by
    intro n
    have hcoe : ((((lpMeas ℝ ℝ (m n) 2 μ).starProjection (hf.toLp f) -
          (lpMeas ℝ ℝ (⨅ k, m k) 2 μ).starProjection (hf.toLp f) : Lp ℝ 2 μ)) : Ω → ℝ)
        =ᵐ[μ] μ[f|m n] - μ[f|⨅ k, m k] := by
      filter_upwards [Lp.coeFn_sub ((lpMeas ℝ ℝ (m n) 2 μ).starProjection (hf.toLp f))
        ((lpMeas ℝ ℝ (⨅ k, m k) 2 μ).starProjection (hf.toLp f)), hae n, haeInf]
        with ω h1 h2 h3
      simp only [Pi.sub_apply, h1, h2, h3]
    rw [← eLpNorm_congr_ae hcoe, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  simp only [heq]
  have hsub : Tendsto (fun n => (lpMeas ℝ ℝ (m n) 2 μ).starProjection (hf.toLp f) -
      (lpMeas ℝ ℝ (⨅ k, m k) 2 μ).starProjection (hf.toLp f)) atTop (𝓝 0) := by
    rw [hGproj]
    simpa using hG.sub (tendsto_const_nhds (x := G))
  have hnorm : Tendsto (fun n => ‖(lpMeas ℝ ℝ (m n) 2 μ).starProjection (hf.toLp f) -
      (lpMeas ℝ ℝ (⨅ k, m k) 2 μ).starProjection (hf.toLp f)‖) atTop (𝓝 0) := by
    simpa using hsub.norm
  simpa using ENNReal.tendsto_ofReal hnorm

end Reverse

end ReflectedGMS.MartingaleLimit
