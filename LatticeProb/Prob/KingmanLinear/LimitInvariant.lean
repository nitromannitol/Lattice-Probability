import Mathlib

/-!
# 5. The limit is invariant, hence constant

The pointwise limsup `x ↦ limsup_n g n x / n` is measurable
(`LatticeProb.measurable_limsup_div`), and it is a.e. subinvariant under a measure-preserving `T`
along which `g` is subadditive (`LatticeProb.limsup_div_le_comp_ae`), from the one-step
subadditivity bound `g (n + 1) x ≤ g 1 x + g n (T x)` transported through the two limits `a n / n`
and `b n / n` by the real-analysis comparison lemma `le_of_tendsto_div_add_le`. Combined with the
ergodic-invariance principle of `LatticeProb.Prob.KingmanLinear.Restated`, this pins the a.e.
limit of `g n x / n` down to a single constant.
-/

open MeasureTheory Filter Topology

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Rewrites `a (n + 1) / ((n + 1 : ℕ) : ℝ)` as `a (n + 1) / ((n : ℝ) + 1)`. -/
private theorem div_cast_succ_eq (a : ℕ → ℝ) (n : ℕ) :
    (fun k : ℕ => a k / (k : ℝ)) (n + 1) = a (n + 1) / ((n : ℝ) + 1) := by
  simp [Nat.cast_add, Nat.cast_one]

/-- Algebraic identity used to match the two sides of the invariance bound at `n + 1`. -/
private theorem div_add_one_add_mul_div_eq (b : ℕ → ℝ) (c : ℝ) {n : ℕ} (hn : n ≠ 0) :
    c / ((n : ℝ) + 1) + b n / (n : ℝ) * ((n : ℝ) / ((n : ℝ) + 1)) = (c + b n) / ((n : ℝ) + 1) := by
  have h : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp

/-- The right side of `div_add_one_add_mul_div_eq` tends to `β` when `b n / n → β`. -/
private theorem tendsto_div_add_one_add_mul_div (b : ℕ → ℝ) (c : ℝ) {β : ℝ}
    (hb : Filter.Tendsto (fun n : ℕ => b n / (n : ℝ)) Filter.atTop (nhds β)) :
    Filter.Tendsto (fun n : ℕ => c / ((n : ℝ) + 1) + b n / (n : ℝ) * ((n : ℝ) / ((n : ℝ) + 1)))
      Filter.atTop (nhds β) := by
  simpa only [div_eq_mul_inv, one_mul, mul_zero, mul_one, zero_add] using
    Filter.Tendsto.add ((tendsto_const_nhds (x := c)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      (Filter.Tendsto.mul hb (tendsto_natCast_div_add_atTop (1 : ℝ)))

/-- `(c + b n) / (n + 1) → β` when `b n / n → β`. -/
private theorem tendsto_add_div_add_one_of_tendsto_div (b : ℕ → ℝ) (c : ℝ) {β : ℝ}
    (hb : Filter.Tendsto (fun n : ℕ => b n / (n : ℝ)) Filter.atTop (nhds β)) :
    Filter.Tendsto (fun n : ℕ => (c + b n) / ((n : ℝ) + 1)) Filter.atTop (nhds β) :=
  Filter.Tendsto.congr'
    (eventually_atTop.2 ⟨1, fun n hn => div_add_one_add_mul_div_eq b c (by omega)⟩)
    (tendsto_div_add_one_add_mul_div b c hb)

/-- `a (n + 1) ≤ c + b n` gives `a (n + 1) / (n + 1) ≤ (c + b n) / (n + 1)`. -/
private theorem div_add_one_le_add_div_add_one (a b : ℕ → ℝ) (c : ℝ)
    (hab : ∀ n, a (n + 1) ≤ c + b n) (n : ℕ) :
    a (n + 1) / ((n : ℝ) + 1) ≤ (c + b n) / ((n : ℝ) + 1) :=
  div_le_div_of_nonneg_right (hab n) (by positivity)

/-- If `a (n + 1) ≤ c + b n` for all `n`, and `a n / n → α`, `b n / n → β`, then `α ≤ β`. -/
private theorem le_of_tendsto_div_add_le {a b : ℕ → ℝ} {c α β : ℝ} (hab : ∀ n, a (n + 1) ≤ c + b n)
    (ha : Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 α))
    (hb : Tendsto (fun n : ℕ => b n / (n : ℝ)) atTop (𝓝 β)) : α ≤ β := by
  have h1 : Filter.Tendsto (fun n : ℕ => a (n + 1) / ((n : ℝ) + 1)) Filter.atTop (nhds α) :=
    Filter.Tendsto.congr' (Eventually.of_forall fun n => div_cast_succ_eq a n)
      (ha.comp (tendsto_add_atTop_nat 1))
  exact le_of_tendsto_of_tendsto' h1 (tendsto_add_div_add_one_of_tendsto_div b c hb)
    (fun n => div_add_one_le_add_div_add_one a b c hab n)


/-- The pointwise limsup `x ↦ limsup_n g n x / n` is measurable. -/
theorem measurable_limsup_div {g : ℕ → Ω → ℝ} (hgm : ∀ n, Measurable (g n)) :
    Measurable (fun x => limsup (fun n : ℕ => g n x / (n : ℝ)) atTop) := by
  exact Measurable.limsup (fun i => (hgm i).div_const _)


/-- The limsup `x ↦ limsup_n g n x / n` is a.e. subinvariant under `T`, from the subadditivity of
`g` at `m = 1`. -/
theorem limsup_div_le_comp_ae {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : ℕ → Ω → ℝ} (hsub : ∀ m n x, g (m+n) x ≤ g m x + g n (T^[m] x))
    (hconv : ∀ᵐ x ∂μ, ∃ L : ℝ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (𝓝 L)) :
    (fun x => limsup (fun n : ℕ => g n x / (n : ℝ)) atTop) ≤ᵐ[μ]
      (fun x => limsup (fun n : ℕ => g n x / (n : ℝ)) atTop) ∘ T := by
  refine (hconv.and (hT.quasiMeasurePreserving.ae hconv)).mono ?_
  rintro x ⟨hx, hTx⟩
  obtain ⟨L, hL⟩ := hx
  obtain ⟨L', hL'⟩ := hTx
  have key : L ≤ L' :=
    le_of_tendsto_div_add_le (a := fun n => g n x) (b := fun n => g n (T x)) (c := g 1 x)
      (fun n => by simpa [Function.iterate_one, Nat.add_comm] using hsub 1 n x) hL hL'
  simpa only [Function.comp_apply, hL.limsup_eq, hL'.limsup_eq] using key

end LatticeProb
