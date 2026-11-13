/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Exist.SupBound at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Field.BandFacts
import LatticeProb.Bonanno.LQGMetric.Gaussian.SupTailField
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueFinite

/-!
# Integrability of the supremum of a band field over a compact set (packet P-X5, T1 input)

Source: planning audit HA5, Details D2 (1) ("`E sup_{[-3,3]^d} |X| < ∞` (D4, chaining)") and D4
(Lemma O); DGZ arXiv:2310.03996, Lemma 2.7 (first paragraph of the proof: the Gaussian tail of the
supremum of the field over a bounded set).

For a continuous version `X` of the band field `H_{a,b}` (`0 < a`, any `b`) and a compact set
`K ⊆ ℝ^d`:

* `Conc.integral_sub_sq_eq`: `E (X z - X w)² = ‖k_{a,b,z} - k_{a,b,w}‖²`;
* `Conc.integral_iSup_le_of_inc`: Fernique–Dudley chaining on `K ⊆ B̄(0, R)`, with the increment
  bound `‖k_z - k_w‖² ≤ L ‖z - w‖² / a²` (`exists_norm_bandVec_sub_sq_le`), bounds the expected
  maximum of every finite family of `±X` on `K`
  (`LQGMetric.SupTail.integral_iSup_family_le`, built on `LQGDimension.ChainBox`);
* `IsBandVersion.integrable_iSup_abs_of_isCompact`: `ω ↦ sup_{z ∈ K} |X z ω|` is integrable
  (`LQGMetric.SupTail.integrable_iSup_of_continuous` for `X` and `-X`).

This is only the crude integrability needed for `log D ∈ L¹` (HA5 D2 (1)); the quantitative sup
and oscillation tails are packet P-OSC's.  The chaining step follows P-OSC's block bound
(`HigherDimLFPP/Field/OscBlock.lean`, `Osc.block_tail`), with the ball `B̄(g, r a)` replaced by an
arbitrary compact set and no base point.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric

namespace HigherDimLFPP

namespace Conc

variable {d : ℕ}

/-! ### Coordinates -/

/-- The sup norm of the coordinates is at most the Euclidean norm. -/
theorem norm_ofLp_sub_le_norm (z w : Rd d) : ‖WithLp.ofLp z - WithLp.ofLp w‖ ≤ ‖z - w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have h := PiLp.norm_apply_le (z - w) i
  simpa only [Pi.sub_apply, PiLp.sub_apply] using h

/-- The Euclidean norm is at most `√d` times the sup norm of the coordinates. -/
theorem norm_sub_le_sqrt_dim_mul (z w : Rd d) :
    ‖z - w‖ ≤ √(d : ℝ) * ‖WithLp.ofLp z - WithLp.ofLp w‖ := by
  have h := norm_toLp_sq_le_dim_mul (d := d) (WithLp.ofLp z - WithLp.ofLp w)
  have e : (WithLp.toLp 2 (WithLp.ofLp z - WithLp.ofLp w) : Rd d) = z - w := by
    rw [← WithLp.ofLp_sub, WithLp.toLp_ofLp]
  rw [e] at h
  have h0 : 0 ≤ √(d : ℝ) * ‖WithLp.ofLp z - WithLp.ofLp w‖ := by positivity
  rw [← Real.sqrt_sq (norm_nonneg (z - w)), ← Real.sqrt_sq h0, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg d)]
  exact Real.sqrt_le_sqrt h

/-! ### Second moments of increments -/

section Band

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {κ : Rd d → ℝ}
  {a b : ℝ} {X : Rd d → Ω → ℝ}

theorem memLp_two_of_isBandVersion (hX : IsBandVersion P W κ a b X) (hW : IsWhiteNoise P W)
    (z : Rd d) : MemLp (X z) 2 P :=
  (hW.memLp _ 2 ENNReal.ofNat_ne_top).ae_eq (hX.ae_eq z).symm

theorem integrable_of_isBandVersion (hX : IsBandVersion P W κ a b X) (hW : IsWhiteNoise P W)
    (z : Rd d) : Integrable (X z) P := by
  have := hW.isProbabilityMeasure
  exact (memLp_two_of_isBandVersion hX hW z).integrable one_le_two

theorem integral_sub_eq_zero (hX : IsBandVersion P W κ a b X) (hW : IsWhiteNoise P W)
    (z w : Rd d) : ∫ ω, (X z ω - X w ω) ∂P = 0 := by
  rw [integral_sub (integrable_of_isBandVersion hX hW z) (integrable_of_isBandVersion hX hW w),
    hX.integral_eq_zero hW, hX.integral_eq_zero hW, sub_zero]

/-- `E (X z - X w)² = ‖k_{a,b,z} - k_{a,b,w}‖²`. -/
theorem integral_sub_sq_eq (hX : IsBandVersion P W κ a b X) (hW : IsWhiteNoise P W)
    (z w : Rd d) :
    ∫ ω, (X z ω - X w ω) ^ 2 ∂P = ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 := by
  rw [← variance_of_integral_eq_zero (hX.hasLaw_sub hW z w).aemeasurable
    (integral_sub_eq_zero hX hW z w), (hX.hasLaw_sub hW z w).variance_eq,
    variance_id_gaussianReal, Real.coe_toNNReal _ (sq_nonneg _)]

end Band

/-! ### Chaining on a compact set -/

section Chain

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : Rd d → ℝ} {a b : ℝ}

/-- **Chaining on a bounded set** (Fernique–Dudley, finite form): if `K ⊆ B̄(0, R)` and a
centered Gaussian process `Y` on `K` has the increments of the band field `H_{a,b}`, whose kernel
vectors satisfy `‖k_z - k_w‖² ≤ L ‖z - w‖² / a²`, then every finite maximum of `Y` has
expectation at most `20 √5 √(2 R L √d / a²) √((d + 1) 2R)`. -/
theorem integral_iSup_le_of_inc {K : Set (Rd d)} {R L : ℝ} (hR : 0 ≤ R) (hL0 : 0 ≤ L)
    (ha : 0 < a) (hKR : ∀ z ∈ K, ‖z‖ ≤ R)
    (hL : ∀ z w : Rd d, ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2)
    {Y : K → Ω → ℝ} (hY : IsGaussianProcess Y P) (hY0 : ∀ z, ∫ ω, Y z ω ∂P = 0)
    (hYinc : ∀ z w : K, ∫ ω, (Y z ω - Y w ω) ^ 2 ∂P =
      ‖bandVec κ a b (z : Rd d) - bandVec κ a b (w : Rd d)‖ ^ 2)
    (n : ℕ) (t : Fin (n + 1) → K) :
    ∫ ω, ⨆ i, Y (t i) ω ∂P ≤
      20 * √5 * √(2 * R * L * √(d : ℝ) / a ^ 2) * √(((d : ℝ) + 1) * (2 * R)) := by
  have hdiam : ∀ z w : K, ‖(z : Rd d) - w‖ ≤ 2 * R := fun z w => by
    calc ‖(z : Rd d) - w‖ ≤ ‖(z : Rd d)‖ + ‖(w : Rd d)‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith [hKR z z.2, hKR w w.2]
  refine LQGMetric.SupTail.integral_iSup_family_le hY hY0 (n := n + 1) (d := d)
    (Nat.succ_pos n) t (fun z => WithLp.ofLp (z : Rd d))
    (L := √(2 * R * L * √(d : ℝ) / a ^ 2)) (a := 2 * R) (Real.sqrt_nonneg _)
    (fun i j => (norm_ofLp_sub_le_norm _ _).trans (hdiam _ _)) (fun i j => ?_)
  rw [hYinc, Real.sq_sqrt (by positivity)]
  set z : Rd d := (t i : Rd d)
  set w : Rd d := (t j : Rd d)
  have h2 : ‖z - w‖ ^ 2 ≤ (2 * R) * (√(d : ℝ) * ‖WithLp.ofLp z - WithLp.ofLp w‖) := by
    rw [sq]
    exact mul_le_mul (hdiam _ _) (norm_sub_le_sqrt_dim_mul z w) (norm_nonneg _) (by positivity)
  calc ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2 := hL z w
    _ ≤ L * ((2 * R) * (√(d : ℝ) * ‖WithLp.ofLp z - WithLp.ofLp w‖)) / a ^ 2 := by gcongr
    _ = 2 * R * L * √(d : ℝ) / a ^ 2 * ‖WithLp.ofLp z - WithLp.ofLp w‖ := by ring

end Chain

/-! ### Suprema of `|X|` over compact sets -/

/-- For a bounded nonempty family, `sup |f| = max (sup f) (sup (-f))`. -/
theorem iSup_abs_eq_max {ι : Type*} [Nonempty ι] {f : ι → ℝ} (hb : BddAbove (range f))
    (hb' : BddAbove (range fun i => -f i)) :
    ⨆ i, |f i| = max (⨆ i, f i) (⨆ i, -f i) := by
  have hb'' : BddAbove (range fun i => |f i|) := by
    obtain ⟨M, hM⟩ := hb
    obtain ⟨M', hM'⟩ := hb'
    refine ⟨max M M', ?_⟩
    rintro _ ⟨i, rfl⟩
    show |f i| ≤ max M M'
    rw [abs_eq_max_neg]
    exact max_le_max (hM ⟨i, rfl⟩) (hM' ⟨i, rfl⟩)
  refine le_antisymm (ciSup_le fun i => ?_) (max_le (ciSup_le fun i => ?_) (ciSup_le fun i => ?_))
  · rw [abs_eq_max_neg]
    exact max_le_max (le_ciSup hb i) (le_ciSup hb' i)
  · exact (le_abs_self (f i)).trans (le_ciSup hb'' i)
  · exact (neg_le_abs (f i)).trans (le_ciSup hb'' i)

/-- A continuous function on a compact set has `|f z| ≤ sup_{K} |f|` at every point of `K`. -/
theorem abs_le_iSup_abs_of_isCompact {K : Set (Rd d)} (hK : IsCompact K) {f : Rd d → ℝ}
    (hf : Continuous f) {z : Rd d} (hz : z ∈ K) : |f z| ≤ ⨆ w : K, |f w| := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hb : BddAbove (range fun w : K => |f w|) :=
    (isCompact_range (continuous_abs.comp (hf.comp continuous_subtype_val))).bddAbove
  exact le_ciSup (f := fun w : K => |f w|) hb ⟨z, hz⟩

end Conc

open Conc

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
  {κ : Rd d → ℝ} {a b : ℝ} {X : Rd d → Ω → ℝ}

/-- **Crude integrability of the supremum** (HA5 D2 (1), D4): for a continuous version `X` of a
band field `H_{a,b}` with `0 < a` and a compact set `K`, `ω ↦ sup_{z ∈ K} |X z ω|` is
integrable. -/
theorem IsBandVersion.integrable_iSup_abs_of_isCompact (hκ : IsLFPPKernel κ)
    (hW : IsWhiteNoise P W) (ha : 0 < a) (hX : IsBandVersion P W κ a b X) {K : Set (Rd d)}
    (hK : IsCompact K) : Integrable (fun ω => ⨆ z : K, |X z ω|) P := by
  have := hW.isProbabilityMeasure
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · have : IsEmpty K := by rw [hK0]; exact Set.isEmpty_coe_sort.2 rfl
    have e : (fun ω => ⨆ z : K, |X z ω|) = fun _ => 0 :=
      funext fun ω => Real.iSup_of_isEmpty _
    rw [e]
    exact integrable_const _
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have : Nonempty K := hKne.to_subtype
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  set R : ℝ := max R₀ 0 with hRdef
  have hR : 0 ≤ R := le_max_right _ _
  have hKR : ∀ z ∈ K, ‖z‖ ≤ R := fun z hz => by
    have h := hR₀ hz
    rw [mem_closedBall, dist_zero_right] at h
    exact h.trans (le_max_left _ _)
  obtain ⟨L, hL0, hL⟩ := exists_norm_bandVec_sub_sq_le hκ
  set Y : K → Ω → ℝ := fun z ω => X z ω with hYdef
  have hY : IsGaussianProcess Y P :=
    (hX.isGaussianProcess hW).comp_right (fun z : K => (z : Rd d))
  have hY0 : ∀ z, ∫ ω, Y z ω ∂P = 0 := fun z => hX.integral_eq_zero hW z
  have hYc : ∀ ω, Continuous fun z => Y z ω := fun ω =>
    (hX.continuous ω).comp continuous_subtype_val
  have hYinc : ∀ z w : K, ∫ ω, (Y z ω - Y w ω) ^ 2 ∂P =
      ‖bandVec κ a b (z : Rd d) - bandVec κ a b (w : Rd d)‖ ^ 2 := fun z w =>
    integral_sub_sq_eq hX hW z w
  have hnY : IsGaussianProcess (fun z ω => -Y z ω) P :=
    LQGMetric.SupTail.isGaussianProcess_neg hY
  have hnY0 : ∀ z, ∫ ω, -Y z ω ∂P = 0 := fun z => by rw [integral_neg, hY0, neg_zero]
  have hnYinc : ∀ z w : K, ∫ ω, (-Y z ω - -Y w ω) ^ 2 ∂P =
      ‖bandVec κ a b (z : Rd d) - bandVec κ a b (w : Rd d)‖ ^ 2 := fun z w => by
    have e : ∀ ω, (-Y z ω - -Y w ω) ^ 2 = (Y z ω - Y w ω) ^ 2 := fun ω => by ring
    simp_rw [e]
    exact hYinc z w
  obtain ⟨hint, -⟩ := LQGMetric.SupTail.integrable_iSup_of_continuous hY hYc
    (integral_iSup_le_of_inc hR hL0 ha hKR (hL a ha b) hY hY0 hYinc)
  obtain ⟨hint', -⟩ := LQGMetric.SupTail.integrable_iSup_of_continuous hnY
    (fun ω => (hYc ω).neg) (integral_iSup_le_of_inc hR hL0 ha hKR (hL a ha b) hnY hnY0 hnYinc)
  have e : (fun ω => ⨆ z : K, |X z ω|) =
      fun ω => max (⨆ z : K, Y z ω) (⨆ z : K, -Y z ω) := by
    funext ω
    exact iSup_abs_eq_max (isCompact_range (hYc ω)).bddAbove
      (isCompact_range (hYc ω).neg).bddAbove
  rw [e]
  exact hint.sup hint'

end HigherDimLFPP
