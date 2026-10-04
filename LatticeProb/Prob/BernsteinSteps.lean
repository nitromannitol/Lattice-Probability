/-
# The bounded Bernstein steps: the one-step estimate and the factorial-moment mgf bound

Route items 4 and 6 of `scratch/pk/bernstein-route.md` for
`LatticeProb.External.Bernstein` / `Parking.External.Bernstein`.

* **Item 4 (`one_step`)** — the filtration instantiation and pull-out of the integrated one-step
  estimate `LatticeProb.integral_abs_add_rpow_le`.
* **Item 6 (`condExp_exp_le_of_factorial`)** — the Step E bound: from the factorial-moment
  bound on a centred increment to the conditional exponential bound, via the factorial series and
  the conditional monotone convergence theorem.

Item 5 (`exists_martingale_rosenthal`, the cumulative Pinelis induction) is the research-level core
and is not attempted here; it remains the exact hypothesis of the final assembly.
-/
import LatticeProb.Prob.BernsteinMartingale

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-! ### Item 4 — the one-step estimate along a filtration -/

/-- The partial sum `∑_{j ∈ Icc 1 i} ξ_j` of a sequence of increments. -/
noncomputable def bernsteinPartialSum (ξ : ℕ → Ω → ℝ) (i : ℕ) : Ω → ℝ :=
  fun ω => ∑ j ∈ Finset.Icc 1 i, ξ j ω

/-- The partial sums satisfy `S (i+1) = S i + ξ (i+1)`. -/
theorem bernsteinPartialSum_succ (ξ : ℕ → Ω → ℝ) (i : ℕ) :
    bernsteinPartialSum ξ (i + 1) = bernsteinPartialSum ξ i + ξ (i + 1) := by
  funext ω
  simp only [bernsteinPartialSum, Pi.add_apply]
  rw [Finset.sum_Icc_succ_top (by omega) (fun j => ξ j ω)]

/-- The cross term `∫ |S|^{p-2} ξ²` equals `∫ |S|^{p-2} μ[ξ² | m]`: the `m`-measurable factor
`|S|^{p-2}` pulls out of the conditional expectation. -/
theorem integral_rpow_mul_condExp_sq_eq' [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) {p : ℝ} {S ξ v : Ω → ℝ}
    (hS : StronglyMeasurable[m] fun ω => |S ω| ^ (p - 2))
    (hv : μ[fun ω => ξ ω ^ 2 | m] =ᵐ[μ] v)
    (hSξ2 : Integrable (fun ω => |S ω| ^ (p - 2) * ξ ω ^ 2) μ)
    (hξ2 : Integrable (fun ω => ξ ω ^ 2) μ) :
    ∫ ω, |S ω| ^ (p - 2) * ξ ω ^ 2 ∂μ = ∫ ω, |S ω| ^ (p - 2) * v ω ∂μ := by
  have hpoint := condExp_mul_of_stronglyMeasurable_left (μ := μ) (m := m) hS hSξ2 hξ2
  have h1 : ∫ ω, |S ω| ^ (p - 2) * ξ ω ^ 2 ∂μ
      = ∫ ω, ((fun ω => |S ω| ^ (p - 2)) * (μ[fun ω => ξ ω ^ 2 | m])) ω ∂μ := by
    calc ∫ ω, |S ω| ^ (p - 2) * ξ ω ^ 2 ∂μ
        = ∫ ω, (μ[fun ω => |S ω| ^ (p - 2) * ξ ω ^ 2 | m]) ω ∂μ :=
          (integral_condExp hm).symm
      _ = ∫ ω, ((fun ω => |S ω| ^ (p - 2)) * (μ[fun ω => ξ ω ^ 2 | m])) ω ∂μ :=
          integral_congr_ae hpoint
  have h2 : ∫ ω, ((fun ω => |S ω| ^ (p - 2)) * (μ[fun ω => ξ ω ^ 2 | m])) ω ∂μ
      = ∫ ω, ((fun ω => |S ω| ^ (p - 2)) * v) ω ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hv] with ω hω
    simp only [Pi.mul_apply]
    rw [hω]
  rw [h1, h2]
  simp only [Pi.mul_apply]

/-- **Item 4, `one_step`.**  For `p ≥ 2` there is a universal `C ≥ 1` such that, along a
filtration `F`, a family `ξ` of martingale differences, and `v i = μ[ξ i² | F (i-1)]`, the partial
sums `S i = ∑_{j=1}^{i} ξ_j` satisfy
`E |S (i+1)|^p ≤ E |S i|^p + C (E[|S i|^{p-2} v (i+1)] + E |ξ (i+1)|^p)`.
The measurability and integrability of the partial sums are taken as hypotheses; the caller
supplies them from the filtration and the moment bounds. -/
theorem one_step {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Ω : Type*} {m₀ : MeasurableSpace Ω} (μ : @Measure Ω m₀) [IsProbabilityMeasure μ]
        (F : Filtration ℕ m₀) (ξ : ℕ → Ω → ℝ) (v : ℕ → Ω → ℝ),
        (∀ i, AEMeasurable (bernsteinPartialSum ξ i) μ) →
        (∀ i, StronglyMeasurable[F i] (fun ω => |bernsteinPartialSum ξ i ω| ^ p)) →
        (∀ i, StronglyMeasurable[F i]
          (fun ω => |bernsteinPartialSum ξ i ω| ^ (p - 2) * bernsteinPartialSum ξ i ω)) →
        (∀ i, StronglyMeasurable[F i] (fun ω => |bernsteinPartialSum ξ i ω| ^ (p - 2))) →
        (∀ i, μ[ξ (i + 1) | F i] =ᵐ[μ] 0) →
        (∀ i, μ[fun ω => ξ (i + 1) ω ^ 2 | F i] =ᵐ[μ] v (i + 1)) →
        (∀ i, Integrable (fun ω => |bernsteinPartialSum ξ i ω| ^ p) μ) →
        (∀ i, Integrable (fun ω => |bernsteinPartialSum ξ i ω| ^ (p - 2)
          * bernsteinPartialSum ξ i ω * ξ (i + 1) ω) μ) →
        (∀ i, Integrable (fun ω => |bernsteinPartialSum ξ i ω| ^ (p - 2)
          * ξ (i + 1) ω ^ 2) μ) →
        (∀ i, Integrable (ξ (i + 1)) μ) →
        (∀ i, Integrable (fun ω => ξ (i + 1) ω ^ 2) μ) →
        (∀ i, Integrable (fun ω => |ξ (i + 1) ω| ^ p) μ) →
        ∀ i,
          ∫ ω, |bernsteinPartialSum ξ (i + 1) ω| ^ p ∂μ
            ≤ ∫ ω, |bernsteinPartialSum ξ i ω| ^ p ∂μ
              + C * (∫ ω, |bernsteinPartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω ∂μ
                + ∫ ω, |ξ (i + 1) ω| ^ p ∂μ) := by
  obtain ⟨C, hC1, hstep⟩ := integral_abs_add_rpow_le hp
  refine ⟨C, hC1, ?_⟩
  intro Ω m₀ μ _ F ξ v hAe hAst hfst hf2st hmean hv hAint hfξ hf2ξ2 hξint hξ2int hξpint i
  have hstep_i := hstep (m := F i) μ (F.le i) (bernsteinPartialSum ξ i) (ξ (i + 1))
    (hAe i) (hAst i) (hfst i) (hmean i) (hAint i) (hfξ i) (hf2ξ2 i)
    (hξint i) (hξ2int i) (hξpint i)
  have hvpull := integral_rpow_mul_condExp_sq_eq' (μ := μ) (m := F i) (F.le i)
    (hf2st i) (hv i) (hf2ξ2 i) (hξ2int i)
  have hSsucc : (fun ω => |bernsteinPartialSum ξ i ω + ξ (i + 1) ω| ^ p)
      = fun ω => |bernsteinPartialSum ξ (i + 1) ω| ^ p := by
    funext ω
    have h := congrFun (bernsteinPartialSum_succ ξ i) ω
    simp only [Pi.add_apply] at h
    rw [← h]
  rw [hSsucc] at hstep_i
  rw [hvpull] at hstep_i
  exact hstep_i


/-! ### Item 6 — the factorial-moment conditional exponential bound -/

/-- The factorial-series form of the exponential. -/
theorem exp_eq_tsum_div' (x : ℝ) :
    Real.exp x = ∑' q : ℕ, x ^ q / (Nat.factorial q : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- **Bernstein Step E, conditional interchange.**  The conditional expectation of the exponential
is the sum of the conditional expectations of its factorial-series terms, by the conditional
monotone convergence theorem `MeasureTheory.condExp_tsum`.  The summability hypothesis is exactly
the one `condExp_tsum` requires; for a factorial-moment bounded `X` it is supplied by the
integrability of `Real.exp (lam * |X|)`. -/
theorem condExp_exp_eq_tsum' {m : MeasurableSpace Ω} (_hm : m ≤ m₀) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable[m₀] X) (lam : ℝ)
    (hsum : ∑' q : ℕ, ∫⁻ ω, ‖(lam * X ω) ^ q / (Nat.factorial q : ℝ)‖ₑ ∂μ ≠ ∞) :
    μ[fun ω => Real.exp (lam * X ω) | m]
      =ᵐ[μ] fun ω => ∑' q : ℕ,
        μ[fun ω => (lam * X ω) ^ q / (Nat.factorial q : ℝ) | m] ω := by
  have hmeas : ∀ q, AEStronglyMeasurable[m₀]
      (fun ω => (lam * X ω) ^ q / (Nat.factorial q : ℝ)) μ :=
    fun q => (((hX.const_mul lam).pow_const q).div_const _).aestronglyMeasurable
  have h := condExp_tsum (μ := μ) (m := m)
    (f := fun q ω => (lam * X ω) ^ q / (Nat.factorial q : ℝ)) hmeas hsum
  have hcongr : μ[fun ω => Real.exp (lam * X ω) | m]
      =ᵐ[μ] μ[fun ω => ∑' q : ℕ, (lam * X ω) ^ q / (Nat.factorial q : ℝ) | m] :=
    condExp_congr_ae (Eventually.of_forall fun ω => exp_eq_tsum_div' _)
  exact hcongr.trans h

/-- **The deterministic Bernstein series bound.**  If the terms `f q` are bounded by `1`, `0` and
the Bernstein coefficients at `q = 0, 1` and at `q >= 2`, and the series is summable, then
summable, then `∑' f q <= exp (lam^2 v / (2 (1 - a lam)))`. -/
theorem tsum_le_exp_bernstein {a v lam : ℝ} (ha : 0 < a) (hv : 0 ≤ v) (hlam : 0 ≤ lam)
    (hlam_a : lam * a < 1) {f : ℕ → ℝ} (hs : Summable f)
    (hf0 : f 0 ≤ 1) (hf1 : f 1 ≤ 0)
    (hf : ∀ q : ℕ, f (q + 2) ≤ lam ^ (q + 2) / (Nat.factorial (q + 2) : ℝ)
      * ((Nat.factorial (q + 2) : ℝ) / 2 * a ^ q * v)) :
    ∑' q, f q ≤ Real.exp (lam ^ 2 * v / (2 * (1 - a * lam))) := by
  -- the tail is dominated by the geometric series
  have hgeom : Summable (fun q : ℕ => lam ^ (q + 2) / (Nat.factorial (q + 2) : ℝ)
      * ((Nat.factorial (q + 2) : ℝ) / 2 * a ^ q * v)) := by
    have hcongr : (fun q : ℕ => lam ^ (q + 2) / (Nat.factorial (q + 2) : ℝ)
        * ((Nat.factorial (q + 2) : ℝ) / 2 * a ^ q * v))
        = fun q : ℕ => (lam ^ 2 * v / 2) * (lam * a) ^ q := by
      funext q
      have hf : (Nat.factorial (q + 2) : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    rw [hcongr]
    exact (summable_geometric_of_lt_one (by positivity) hlam_a).mul_left _
  have htail : ∑' q : ℕ, f (q + 2) ≤ ∑' q : ℕ, lam ^ (q + 2) / (Nat.factorial (q + 2) : ℝ)
      * ((Nat.factorial (q + 2) : ℝ) / 2 * a ^ q * v) :=
    Summable.tsum_le_tsum hf ((summable_nat_add_iff 2).mpr hs) hgeom
  have htailval : ∑' q : ℕ, lam ^ (q + 2) / (Nat.factorial (q + 2) : ℝ)
      * ((Nat.factorial (q + 2) : ℝ) / 2 * a ^ q * v) = lam ^ 2 * v / (2 * (1 - a * lam)) := by
    have hcongr : (fun q : ℕ => lam ^ (q + 2) / (Nat.factorial (q + 2) : ℝ)
        * ((Nat.factorial (q + 2) : ℝ) / 2 * a ^ q * v))
        = fun q : ℕ => (lam ^ 2 * v / 2) * (lam * a) ^ q := by
      funext q
      have hf : (Nat.factorial (q + 2) : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    rw [hcongr, tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hlam_a]
    have hne : (1 : ℝ) - lam * a ≠ 0 := by linarith
    field_simp
  have hsplit : ∑' q, f q = f 0 + f 1 + ∑' q : ℕ, f (q + 2) := by
    rw [hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
    ring
  rw [hsplit]
  have hmono : f 0 + f 1 ≤ 1 + 0 := add_le_add hf0 hf1
  calc f 0 + f 1 + ∑' q : ℕ, f (q + 2)
      ≤ 1 + 0 + lam ^ 2 * v / (2 * (1 - a * lam)) := by
        have := htail.trans_eq htailval
        linarith
    _ = 1 + lam ^ 2 * v / (2 * (1 - a * lam)) := by ring
    _ ≤ Real.exp (lam ^ 2 * v / (2 * (1 - a * lam))) := by
        have := Real.add_one_le_exp (lam ^ 2 * v / (2 * (1 - a * lam)))
        linarith


/-- **Item 6, `condExp_exp_le_of_factorial`.**  From the conditional factorial-moment bound on a
centred increment `X` — the `q = 0, 1` terms bounded by `1` and `0`, the `q >= 2` terms by the
Bernstein coefficients `(q!/2) a^{q-2} v` — the conditional exponential moment is bounded by the
Bernstein exponent `exp (lam^2 v / (2 (1 - a lam)))`.  The conditional interchange is
`condExp_exp_eq_tsum'` and the deterministic series assembly is `tsum_le_exp_bernstein`. -/
theorem condExp_exp_le_of_factorial {m : MeasurableSpace Ω} (hm : m ≤ m₀) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {a v lam : ℝ} (ha : 0 < a) (hv : 0 ≤ v) (hlam : 0 ≤ lam) (hlam_a : lam * a < 1)
    (hX : Measurable[m₀] X)
    (h0 : μ[fun ω => (lam * X ω) ^ 0 / (Nat.factorial 0 : ℝ) | m] ≤ᵐ[μ] fun _ => 1)
    (h1 : μ[fun ω => (lam * X ω) ^ 1 / (Nat.factorial 1 : ℝ) | m] ≤ᵐ[μ] fun _ => 0)
    (hterm : ∀ q : ℕ, 2 ≤ q → μ[fun ω => (lam * X ω) ^ q / (Nat.factorial q : ℝ) | m] ≤ᵐ[μ]
      fun _ => lam ^ q / (Nat.factorial q : ℝ) * ((Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v))
    (hsumm : ∀ᵐ ω ∂μ, Summable
      (fun q : ℕ => μ[fun ω' => (lam * X ω') ^ q / (Nat.factorial q : ℝ) | m] ω))
    (hsum : ∑' q : ℕ, ∫⁻ ω, ‖(lam * X ω) ^ q / (Nat.factorial q : ℝ)‖ₑ ∂μ ≠ ∞) :
    μ[fun ω => Real.exp (lam * X ω) | m] ≤ᵐ[μ]
      fun _ => Real.exp (lam ^ 2 * v / (2 * (1 - a * lam))) := by
  have hinter := condExp_exp_eq_tsum' hm hX lam hsum
  have hb : ∀ q : ℕ, ∀ᵐ ω ∂μ,
      (μ[fun ω' => (lam * X ω') ^ q / (Nat.factorial q : ℝ) | m]) ω
        ≤ (if q = 0 then 1 else if q = 1 then 0
          else lam ^ q / (Nat.factorial q : ℝ)
            * ((Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v)) := by
    intro q
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      simp only [if_pos rfl]
      exact h0
    · by_cases hq2 : 2 ≤ q
      · have hq0 : q ≠ 0 := by omega
        have hq1 : q ≠ 1 := by omega
        simp only [if_neg hq0, if_neg hq1]
        exact hterm q hq2
      · have hq1 : q = 1 := by omega
        subst hq1
        simp only [if_neg (by norm_num : (1 : ℕ) ≠ 0), if_pos rfl]
        exact h1
  have hall : ∀ᵐ ω ∂μ, ∀ q : ℕ,
      (μ[fun ω' => (lam * X ω') ^ q / (Nat.factorial q : ℝ) | m]) ω
        ≤ (if q = 0 then 1 else if q = 1 then 0
          else lam ^ q / (Nat.factorial q : ℝ) * ((Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v)) :=
    (MeasureTheory.ae_all_iff (p := fun ω q =>
      (μ[fun ω' => (lam * X ω') ^ q / (Nat.factorial q : ℝ) | m]) ω
        ≤ (if q = 0 then 1 else if q = 1 then 0
          else lam ^ q / (Nat.factorial q : ℝ)
            * ((Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v)))).mpr hb
  filter_upwards [hinter, hall, hsumm] with ω hinterω hallω hsummω
  rw [hinterω]
  exact tsum_le_exp_bernstein ha hv hlam hlam_a hsummω (hallω 0) (hallω 1) (fun q => hallω (q + 2))


#print axioms LatticeProb.one_step
#print axioms LatticeProb.exp_eq_tsum_div'
#print axioms LatticeProb.condExp_exp_eq_tsum'
#print axioms LatticeProb.tsum_le_exp_bernstein
#print axioms LatticeProb.condExp_exp_le_of_factorial

end LatticeProb
