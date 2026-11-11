import Mathlib
import LatticeProb.Gauss.GFF

/-!
# Events with polynomially high probability

Adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795],
Lemma 2.4, for the predicate `PolyHighProb` (module `LatticeProb.Gauss.GFF`). Elementary closure properties: monotonicity, finite intersections, linear and
power reparametrization of the scale, the Borel-Cantelli lemma along the dyadic scales `ε = 2^{-k}`, and the union bound
over the dyadic scales below a power of `r` (Berestycki-Powell, *Gaussian free field, Liouville quantum gravity and
Gaussian multiplicative chaos*, for the polynomial high-probability convention; Duplantier-Sheffield 2011 for the dyadic
scales).
-/

namespace LatticeProb.LQG.LQGMeasureNonatomicMass

open MeasureTheory Filter Set Topology LatticeProb.Gauss
open scoped ENNReal

/-- For `a > 0` and `c > 0`, `r^a ≤ c` for all small `r > 0`. -/
theorem exists_pos_forall_rpow_le {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∃ r₁ > 0, ∀ r : ℝ, 0 < r → r < r₁ → r ^ a ≤ c := by
  refine ⟨c ^ a⁻¹, Real.rpow_pos_of_pos hc _, fun r hr hr₁ => ?_⟩
  calc r ^ a ≤ (c ^ a⁻¹) ^ a := Real.rpow_le_rpow hr.le hr₁.le ha.le
    _ = c := by rw [← Real.rpow_mul hc.le, inv_mul_cancel₀ ha.ne', Real.rpow_one]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω}

/-- Real reparametrization of the scale: `r ↦ E(r^a)` for `a > 0`. -/
theorem polyHighProb_comp_rpow (h : PolyHighProb P E) {a : ℝ} (ha : 0 < a) :
    PolyHighProb P fun r => E (r ^ a) := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  obtain ⟨r₁, hr₁, h1⟩ := exists_pos_forall_rpow_le ha (half_pos hr₀)
  refine ⟨a * p, mul_pos ha hp, C, r₁, hr₁, fun r hr hrr => ?_⟩
  calc P (E (r ^ a))ᶜ ≤ ENNReal.ofReal (C * (r ^ a) ^ p) :=
        hE _ (Real.rpow_pos_of_pos hr _) ((h1 r hr hrr).trans_lt (half_lt_self hr₀))
    _ = ENNReal.ofReal (C * r ^ (a * p)) := by rw [← Real.rpow_mul hr.le]

/-- An event containing, at all small scales, an event of polynomially high probability has polynomially high
probability. -/
theorem polyHighProb_mono_of_small (h : PolyHighProb P E) {r₁ : ℝ} (hr₁ : 0 < r₁)
    (hEF : ∀ r, 0 < r → r < r₁ → E r ⊆ F r) : PolyHighProb P F := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  refine ⟨p, hp, C, min r₀ r₁, lt_min hr₀ hr₁, fun r hr hrr => ?_⟩
  calc P (F r)ᶜ ≤ P (E r)ᶜ :=
        measure_mono (compl_subset_compl.2 (hEF r hr (hrr.trans_le (min_le_right _ _))))
    _ ≤ _ := hE r hr (hrr.trans_le (min_le_left _ _))

theorem polyHighProb_mono (h : PolyHighProb P E) (hEF : ∀ r, E r ⊆ F r) : PolyHighProb P F :=
  polyHighProb_mono_of_small h one_pos fun r _ _ => hEF r

/-- Linear reparametrization of the scale: `r ↦ E(c r)` for a constant `c > 0`. -/
theorem polyHighProb_comp_mul (h : PolyHighProb P E) {c : ℝ} (hc : 0 < c) :
    PolyHighProb P fun r => E (c * r) := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  refine ⟨p, hp, C * c ^ p, r₀ / c, div_pos hr₀ hc, fun r hr hrr => ?_⟩
  have hcr : c * r < r₀ := by rwa [lt_div_iff₀ hc, mul_comm] at hrr
  calc P (E (c * r))ᶜ ≤ ENNReal.ofReal (C * (c * r) ^ p) := hE _ (mul_pos hc hr) hcr
    _ = ENNReal.ofReal (C * c ^ p * r ^ p) := by rw [Real.mul_rpow hc.le hr.le, mul_assoc]

/-- The intersection of two events of polynomially high probability. -/
theorem polyHighProb_inter (hE : PolyHighProb P E) (hF : PolyHighProb P F) :
    PolyHighProb P fun r => E r ∩ F r := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := hE
  obtain ⟨q, hq, D, s₀, hs₀, hF⟩ := hF
  refine ⟨min p q, lt_min hp hq, max C 0 + max D 0, min (min r₀ s₀) 1,
    lt_min (lt_min hr₀ hs₀) one_pos, fun r hr hrr => ?_⟩
  have hr₀' : r < r₀ := hrr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hs₀' : r < s₀ := hrr.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hr1 : r < 1 := hrr.trans_le (min_le_right _ _)
  have hpr : r ^ p ≤ r ^ min p q := Real.rpow_le_rpow_of_exponent_ge hr hr1.le (min_le_left _ _)
  have hqr : r ^ q ≤ r ^ min p q := Real.rpow_le_rpow_of_exponent_ge hr hr1.le (min_le_right _ _)
  have hC : C * r ^ p ≤ max C 0 * r ^ min p q :=
    mul_le_mul (le_max_left _ _) hpr (by positivity) (le_max_right _ _)
  have hD : D * r ^ q ≤ max D 0 * r ^ min p q :=
    mul_le_mul (le_max_left _ _) hqr (by positivity) (le_max_right _ _)
  rw [compl_inter]
  calc P ((E r)ᶜ ∪ (F r)ᶜ) ≤ P (E r)ᶜ + P (F r)ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C * r ^ p) + ENNReal.ofReal (D * r ^ q) :=
        add_le_add (hE r hr hr₀') (hF r hr hs₀')
    _ ≤ ENNReal.ofReal (max C 0 * r ^ min p q) + ENNReal.ofReal (max D 0 * r ^ min p q) :=
        add_le_add (ENNReal.ofReal_le_ofReal hC) (ENNReal.ofReal_le_ofReal hD)
    _ = ENNReal.ofReal ((max C 0 + max D 0) * r ^ min p q) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_mul]

/-- **Borel-Cantelli along the dyadic scales.** If `E` has polynomially high probability, then almost surely
`ω ∈ E(2^{-k})` for all large `k`: the failure probabilities `O(2^{-kp})` are summable. -/
theorem polyHighProb_ae_eventually_dyadic (h : PolyHighProb P E) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ω ∈ E ((2 : ℝ)⁻¹ ^ k) := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one hr₀ (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hq : (2 : ℝ)⁻¹ ^ p < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
  have hterm : ∀ n : ℕ, P (E ((2 : ℝ)⁻¹ ^ (n + k₀)))ᶜ ≤
      ENNReal.ofReal (max C 0) * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ p) ^ n := by
    intro n
    have hpos : 0 < (2 : ℝ)⁻¹ ^ (n + k₀) := by positivity
    have hlt : (2 : ℝ)⁻¹ ^ (n + k₀) < r₀ :=
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left k₀ n)).trans_lt hk₀
    have hle : ((2 : ℝ)⁻¹ ^ (n + k₀)) ^ p ≤ ((2 : ℝ)⁻¹ ^ p) ^ n := by
      rw [← Real.rpow_pow_comm (by norm_num)]
      exact pow_le_pow_of_le_one (Real.rpow_nonneg (by norm_num) _) hq.le (Nat.le_add_right n k₀)
    calc P (E ((2 : ℝ)⁻¹ ^ (n + k₀)))ᶜ ≤ ENNReal.ofReal (C * ((2 : ℝ)⁻¹ ^ (n + k₀)) ^ p) :=
          hE _ hpos hlt
      _ ≤ ENNReal.ofReal (max C 0 * ((2 : ℝ)⁻¹ ^ p) ^ n) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul (le_max_left _ _) hle
            (by positivity) (le_max_right _ _))
      _ = _ := by
          rw [ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_pow (by positivity)]
  have hsum : ∑' n : ℕ, P (E ((2 : ℝ)⁻¹ ^ (n + k₀)))ᶜ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 ?_)
    exact (tsub_pos_of_lt (ENNReal.ofReal_lt_one.2 hq)).ne'
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  rw [eventually_atTop] at hω ⊢
  obtain ⟨N, hN⟩ := hω
  refine ⟨N + k₀, fun k hk => ?_⟩
  have h' := hN (k - k₀) (by omega)
  rw [Nat.sub_add_cancel (by omega : k₀ ≤ k)] at h'
  simpa using h'

/-! ### Small-scale bookkeeping -/

/-- If `b < a`, then `C ε^a ≤ ε^b` for all small `ε > 0`. -/
theorem eventually_mul_rpow_le (C : ℝ) {a b : ℝ} (hab : b < a) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), C * ε ^ a ≤ ε ^ b := by
  have hC1 : (0 : ℝ) < max C 0 + 1 := by positivity
  obtain ⟨r₁, hr₁, h⟩ := exists_pos_forall_rpow_le (sub_pos.2 hab) (inv_pos.2 hC1)
  filter_upwards [Ioo_mem_nhdsGT hr₁] with ε hε
  have hε0 : 0 < ε := hε.1
  have h1 : ε ^ (a - b) ≤ (max C 0 + 1)⁻¹ := h ε hε.1 hε.2
  have hsplit : ε ^ a = ε ^ (a - b) * ε ^ b := by rw [← Real.rpow_add hε0, sub_add_cancel]
  have hb : 0 < ε ^ b := Real.rpow_pos_of_pos hε0 _
  have hab' : 0 < ε ^ (a - b) := Real.rpow_pos_of_pos hε0 _
  rw [hsplit]
  calc C * (ε ^ (a - b) * ε ^ b) ≤ (max C 0 + 1) * (ε ^ (a - b) * ε ^ b) := by
        gcongr; exact (le_max_left C 0).trans (le_add_of_nonneg_right zero_le_one)
    _ ≤ (max C 0 + 1) * ((max C 0 + 1)⁻¹ * ε ^ b) := by gcongr
    _ = ε ^ b := by rw [← mul_assoc, mul_inv_cancel₀ hC1.ne', one_mul]

/-- If `a < b` and `c > 0`, then `ε^b ≤ c ε^a` for all small `ε > 0`. -/
theorem eventually_rpow_le_mul {c : ℝ} (hc : 0 < c) {a b : ℝ} (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ b ≤ c * ε ^ a := by
  filter_upwards [eventually_mul_rpow_le c⁻¹ hab] with ε hε
  calc ε ^ b = c * (c⁻¹ * ε ^ b) := by rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    _ ≤ c * ε ^ a := by gcongr

/-- A property holding at all small scales `r > 0` along `𝓝[>] 0` holds on some interval `(0, r₁)`. -/
theorem exists_pos_of_eventually_nhdsGT {p : ℝ → Prop} (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), p r) :
    ∃ r₁ > 0, ∀ r : ℝ, 0 < r → r < r₁ → p r := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  exact ⟨u, hu, fun r hr hru => hsub ⟨hr, hru⟩⟩

/-- Monotonicity for events compared only at small scales, in filter form. -/
theorem polyHighProb_mono_of_eventually (h : PolyHighProb P E)
    (hEF : ∀ᶠ r in 𝓝[>] (0 : ℝ), E r ⊆ F r) : PolyHighProb P F := by
  obtain ⟨r₁, hr₁, h'⟩ := exists_pos_of_eventually_nhdsGT hEF
  exact polyHighProb_mono_of_small h hr₁ h'

/-- Intersecting with an almost sure event does not change the failure probabilities. -/
theorem polyHighProb_inter_ae (h : PolyHighProb P E) {W : Set Ω} (hW : ∀ᵐ ω ∂P, ω ∈ W) :
    PolyHighProb P fun r => E r ∩ W := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  have hW0 : P Wᶜ = 0 := ae_iff.1 hW
  refine ⟨p, hp, C, r₀, hr₀, fun r hr hrr => ?_⟩
  rw [compl_inter]
  calc P ((E r)ᶜ ∪ Wᶜ) ≤ P (E r)ᶜ + P Wᶜ := measure_union_le _ _
    _ = P (E r)ᶜ := by rw [hW0, add_zero]
    _ ≤ _ := hE r hr hrr

/-- **Union bound over the dyadic scales below a power of `r`.** If `E` has polynomially high probability, so has the
event that `E(2^{-j})` holds for every dyadic scale `2^{-j} ≤ c r^a` (`a, c > 0`): the failure probabilities
`O(2^{-jp})` sum to `O((c r^a)^p)`. -/
theorem polyHighProb_dyadic_tail (h : PolyHighProb P E) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    PolyHighProb P fun r => {ω | ∀ j : ℕ, (2 : ℝ)⁻¹ ^ j ≤ c * r ^ a → ω ∈ E ((2 : ℝ)⁻¹ ^ j)} := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  set q : ℝ := (2 : ℝ)⁻¹ ^ p with hq_def
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
  obtain ⟨r₁, hr₁, hsmall⟩ :=
    exists_pos_forall_rpow_le ha (div_pos hr₀ (by positivity : (0 : ℝ) < 2 * c))
  refine ⟨a * p, mul_pos ha hp, max C 0 / (1 - q) * c ^ p, r₁, hr₁, fun r hr hrr => ?_⟩
  set x : ℝ := c * r ^ a with hx_def
  have hx0 : 0 < x := mul_pos hc (Real.rpow_pos_of_pos hr _)
  have hxr₀ : x < r₀ := by
    have := hsmall r hr hrr
    calc x ≤ c * (r₀ / (2 * c)) := mul_le_mul_of_nonneg_left this hc.le
      _ = r₀ / 2 := by field_simp
      _ < r₀ := by linarith
  have hex : ∃ j : ℕ, (2 : ℝ)⁻¹ ^ j ≤ x := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx0 (by norm_num : (2 : ℝ)⁻¹ < 1)
    exact ⟨n, hn.le⟩
  classical
  set J := Nat.find hex with hJ
  have hJx : (2 : ℝ)⁻¹ ^ J ≤ x := Nat.find_spec hex
  have hsub : {ω | ∀ j : ℕ, (2 : ℝ)⁻¹ ^ j ≤ c * r ^ a → ω ∈ E ((2 : ℝ)⁻¹ ^ j)}ᶜ ⊆
      ⋃ n : ℕ, (E ((2 : ℝ)⁻¹ ^ (J + n)))ᶜ := by
    intro ω hω
    simp only [mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hω
    obtain ⟨j, hj, hjE⟩ := hω
    have hJj : J ≤ j := Nat.find_min' hex hj
    exact mem_iUnion.2 ⟨j - J, by rwa [Nat.add_sub_cancel' hJj]⟩
  have hterm : ∀ n : ℕ, P (E ((2 : ℝ)⁻¹ ^ (J + n)))ᶜ ≤
      ENNReal.ofReal (max C 0 * ((2 : ℝ)⁻¹ ^ J) ^ p) * ENNReal.ofReal q ^ n := by
    intro n
    have hpos : 0 < (2 : ℝ)⁻¹ ^ (J + n) := by positivity
    have hlt : (2 : ℝ)⁻¹ ^ (J + n) < r₀ :=
      ((pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right J n)).trans hJx).trans_lt hxr₀
    calc P (E ((2 : ℝ)⁻¹ ^ (J + n)))ᶜ ≤ ENNReal.ofReal (C * ((2 : ℝ)⁻¹ ^ (J + n)) ^ p) := hE _ hpos hlt
      _ ≤ ENNReal.ofReal (max C 0 * ((2 : ℝ)⁻¹ ^ (J + n)) ^ p) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      _ = _ := by
          rw [← ENNReal.ofReal_pow hq0, ← ENNReal.ofReal_mul (by positivity), pow_add,
            Real.mul_rpow (by positivity) (by positivity), hq_def, Real.rpow_pow_comm (by norm_num)]
          ring_nf
  calc P {ω | ∀ j : ℕ, (2 : ℝ)⁻¹ ^ j ≤ c * r ^ a → ω ∈ E ((2 : ℝ)⁻¹ ^ j)}ᶜ
      ≤ ∑' n : ℕ, P (E ((2 : ℝ)⁻¹ ^ (J + n)))ᶜ := (measure_mono hsub).trans (measure_iUnion_le _)
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (max C 0 * ((2 : ℝ)⁻¹ ^ J) ^ p) * ENNReal.ofReal q ^ n :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (max C 0 * ((2 : ℝ)⁻¹ ^ J) ^ p) * (1 - ENNReal.ofReal q)⁻¹ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ = ENNReal.ofReal (max C 0 * ((2 : ℝ)⁻¹ ^ J) ^ p / (1 - q)) := by
        rw [div_eq_mul_inv, ENNReal.ofReal_mul' (q := (1 - q)⁻¹) (inv_nonneg.2 (by linarith)),
          ENNReal.ofReal_inv_of_pos (by linarith), ENNReal.ofReal_sub _ hq0, ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (max C 0 / (1 - q) * c ^ p * r ^ (a * p)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hxp : ((2 : ℝ)⁻¹ ^ J) ^ p ≤ x ^ p := Real.rpow_le_rpow (by positivity) hJx hp.le
        have hxp' : x ^ p = c ^ p * r ^ (a * p) := by
          rw [hx_def, Real.mul_rpow hc.le (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le]
        have h1q : 0 < 1 - q := by linarith
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_assoc, ← hxp']
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxp (le_max_right _ _)) h1q.le

end LatticeProb.LQG.LQGMeasureNonatomicMass
