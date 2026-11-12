/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordVarianceAux2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordVarianceAux1

/-!
# Node `V47`, auxiliary file 2: growth and couplings of the local configurations

For every configuration of the normalized local families (`smallFamily`, `largeFamily`) we
verify the hypotheses of Lemma 3.1 (`CfgGood`):

* chord and child polygon are probability combinations;
* both have growth constant `7 g`, `g = gFactor M δ (1/32) k`, at scale `1`.  For small excess
  with `δ²(k+1) ≤ 1/(32M)` every edge advances along the chord (forward-edge lemma), and the
  growth constant is universal; otherwise it is `O(M)` because there are at most `3M` edges;
* chord and polygon can be coupled within `6 δ √(k+1)`.  For small excess this comes from the
  vertex estimate `|z_i - (x + τ_i (y - x))|² ≤ (S² - R²)/4`, where `τ_i` is the normalized
  arclength of the vertex `z_i`, and `S² - R² ≤ 20 R² A`.

Finally `CfgGood` is transported to similarity images (`cfgGood_cfgMap`).
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.RecVar

open Blueprint.Draft

/-- The hypotheses of Lemma 3.1 for the chord/polygon pair of a configuration: probability
combinations, growth `L min(1, t/R)`, and a coupling within `u`. -/
def CfgGood (L R u : ℝ) (c : Config) : Prop :=
  (polyComb c.1).IsProb ∧ (polyComb c.2).IsProb ∧ GrowthBound (polyComb c.1).toMeasure L R ∧
    GrowthBound (polyComb c.2).toMeasure L R ∧
    CoupledWithin (polyComb c.1).toMeasure (polyComb c.2).toMeasure u

/-! ## Elementary estimates -/

/-- If `|d| ≤ τ S` and `|d - v| ≤ (1 - τ) S`, then `d` is within `√(S² - |v|²)/2` of `τ v`. -/
lemma vert_close (d v : ℂ) {τ S : ℝ} (h1 : ‖d‖ ≤ τ * S) (h2 : ‖d - v‖ ≤ (1 - τ) * S)
    (hS : ‖v‖ ≤ S) : ‖d - (τ : ℂ) * v‖ ^ 2 ≤ (S ^ 2 - ‖v‖ ^ 2) / 4 := by
  have hS0 : 0 ≤ S := (norm_nonneg _).trans hS
  have hX : 0 ≤ S ^ 2 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  rcases eq_or_lt_of_le hS0 with hS0' | hSpos
  · subst hS0'
    have hd : d = 0 := norm_le_zero_iff.1 (by simpa using h1)
    have hv : v = 0 := norm_le_zero_iff.1 hS
    subst hd; subst hv; simp
  · have h0τ : 0 ≤ τ := by
      by_contra h; push Not at h; nlinarith [norm_nonneg d]
    have h1τ : 0 ≤ 1 - τ := by
      by_contra h; push Not at h; nlinarith [norm_nonneg (d - v)]
    have hid : ‖d - (τ : ℂ) * v‖ ^ 2 =
        (1 - τ) * ‖d‖ ^ 2 + τ * ‖d - v‖ ^ 2 - τ * (1 - τ) * ‖v‖ ^ 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have e1 : ‖d‖ ^ 2 ≤ (τ * S) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have e2 : ‖d - v‖ ^ 2 ≤ ((1 - τ) * S) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have e3 : (1 - τ) * ‖d‖ ^ 2 + τ * ‖d - v‖ ^ 2 ≤
        (1 - τ) * (τ * S) ^ 2 + τ * ((1 - τ) * S) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left e1 h1τ) (mul_le_mul_of_nonneg_left e2 h0τ)
    rw [hid]
    nlinarith [mul_nonneg (sq_nonneg (τ - 1 / 2)) hX]

/-- Excess estimates: with `A = log (S/ρ) ∈ [0,1]`, `S - ρ ≤ 4 ρ A` and `S² - ρ² ≤ 20 ρ² A`. -/
lemma excess_facts {S ρ : ℝ} (hρ : 0 < ρ) (hS : 0 < S) (hA0 : 0 ≤ Real.log (S / ρ))
    (hA1 : Real.log (S / ρ) ≤ 1) :
    S - ρ ≤ 4 * ρ * Real.log (S / ρ) ∧ S ^ 2 - ρ ^ 2 ≤ 20 * ρ ^ 2 * Real.log (S / ρ) := by
  set A := Real.log (S / ρ) with hA
  have hE : S / ρ = Real.exp A := (Real.exp_log (div_pos hS hρ)).symm
  have hSE : S = ρ * Real.exp A := by rw [← hE]; field_simp
  have hE1 : 1 ≤ Real.exp A := Real.one_le_exp hA0
  have hE3 : Real.exp A ≤ 4 := by
    have h1 := TwoScale.exp_half_lt_two
    have h2 : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
      rw [← Real.exp_add]; norm_num
    have h := Real.exp_le_exp.2 hA1
    nlinarith [Real.exp_pos (1 / 2)]
  have hEA : Real.exp A - 1 ≤ A * Real.exp A := by
    have h := Real.add_one_le_exp (-A)
    have h2 : Real.exp (-A) * Real.exp A = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos A]
  have hAE : A * Real.exp A ≤ A * 4 := mul_le_mul_of_nonneg_left hE3 hA0
  constructor
  · rw [hSE]
    have := mul_le_mul_of_nonneg_left (hEA.trans hAE) hρ.le
    linarith
  · rw [hSE]
    have h3 : (Real.exp A - 1) * (Real.exp A + 1) ≤ A * 4 * (Real.exp A + 1) :=
      mul_le_mul_of_nonneg_right (hEA.trans hAE) (by linarith)
    have h4 : A * 4 * (Real.exp A + 1) ≤ A * 4 * 5 :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h5 := mul_le_mul_of_nonneg_left (h3.trans h4) (sq_nonneg ρ)
    nlinarith

lemma toMeasure_le_one {c : SegComb} (hc : c.IsProb) (B : Set ℂ) : c.toMeasure B ≤ 1 := by
  have h := TwoScale.toMeasure_real_univ c hc.1
  rw [hc.2, measureReal_def] at h
  have hu : c.toMeasure univ = 1 := (ENNReal.toReal_eq_one_iff _).1 h
  rw [← hu]
  exact measure_mono (subset_univ _)

/-! ## Polygons given by vertex functions -/

/-- Edge lengths. -/
def ell (V : ℕ → ℂ) (i : ℕ) : ℝ := ‖V (i + 1) - V i‖

/-- Partial lengths. -/
def plen (V : ℕ → ℂ) (i : ℕ) : ℝ := ∑ j ∈ Finset.range i, ell V j

lemma plen_succ (V : ℕ → ℂ) (i : ℕ) : plen V (i + 1) = plen V i + ell V i :=
  Finset.sum_range_succ _ _

lemma plen_mono (V : ℕ → ℂ) (i : ℕ) : plen V i ≤ plen V (i + 1) := by
  rw [plen_succ]; exact le_add_of_nonneg_right (norm_nonneg _)

lemma norm_sub_V0_le (V : ℕ → ℂ) (i : ℕ) : ‖V i - V 0‖ ≤ plen V i := by
  rw [← Finset.sum_range_sub (fun j => V j) i]
  exact norm_sum_le _ _

lemma norm_Vm_sub_le (V : ℕ → ℂ) {i m : ℕ} (hi : i ≤ m) :
    ‖V m - V i‖ ≤ plen V m - plen V i := by
  have e : V m - V i = ∑ j ∈ Finset.Ico i m, (V (j + 1) - V j) := by
    rw [Finset.sum_Ico_eq_sub _ hi, Finset.sum_range_sub, Finset.sum_range_sub]; abel
  rw [e, plen, plen, ← Finset.sum_Ico_eq_sub _ hi]
  exact norm_sum_le _ _

/-- The polygon weights `ℓ_i / S`. -/
def pw (V : ℕ → ℂ) (m : ℕ) (i : ℕ) : ℝ := ell V i / plen V m

lemma isProb_poly (V : ℕ → ℂ) {m : ℕ} (hS : 0 < plen V m) : (ConstrCov.wc m (pw V m) V).IsProb :=
  ConstrCov.isProb_wc V (fun i _ => div_nonneg (norm_nonneg _) hS.le)
    (by simp only [pw]; rw [← Finset.sum_div]; exact div_self hS.ne')

/-- **Coupling of a polygon with its chord** through normalized arclength. -/
lemma coupled_poly (V : ℕ → ℂ) {m : ℕ} (hS : 0 < plen V m) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : (plen V m ^ 2 - ‖V m - V 0‖ ^ 2) / 4 ≤ u ^ 2) :
    CoupledWithin (ConstrCov.segMeas (V 0) (V m)) (ConstrCov.wc m (pw V m) V).toMeasure u := by
  set S := plen V m with hSdef
  set τ : ℕ → ℝ := fun i => plen V i / S with hτdef
  have hτ : ∀ i, τ i ≤ τ (i + 1) := fun i => div_le_div_of_nonneg_right (plen_mono V i) hS.le
  have hW : ∀ i, pw V m i = τ (i + 1) - τ i := fun i => by
    simp only [pw, τ, plen_succ]; ring
  have hsplit := toMeasure_wc_lin (V 0) (V m) τ hτ m (pw V m) hW
  have h0 : τ 0 = 0 := by simp [τ, plen]
  have h1 : τ m = 1 := div_self hS.ne'
  rw [h0, h1] at hsplit
  have hseg : (volume.restrict (Icc (0 : ℝ) 1)).map (lin (V 0) (V m)) =
      ConstrCov.segMeas (V 0) (V m) := rfl
  rw [hseg] at hsplit
  rw [← hsplit]
  refine ConstrCov.coupled_wc fun i hi => ?_
  have hρS : ‖V m - V 0‖ ≤ S := norm_sub_V0_le V m
  have hτS : τ i * S = plen V i := div_mul_cancel₀ _ hS.ne'
  have hc := vert_close (V i - V 0) (V m - V 0) (τ := τ i) (S := S)
    (by rw [hτS]; exact norm_sub_V0_le V i)
    (by
      rw [sub_mul, one_mul, hτS, show V i - V 0 - (V m - V 0) = -(V m - V i) by ring, norm_neg]
      exact norm_Vm_sub_le V hi)
    hρS
  have e : ‖lin (V 0) (V m) (τ i) - V i‖ = ‖V i - V 0 - (τ i : ℂ) * (V m - V 0)‖ := by
    rw [← norm_neg]; congr 1; simp only [lin]; ring
  rw [e]
  have hsq : ‖V i - V 0 - (τ i : ℂ) * (V m - V 0)‖ ^ 2 ≤ u ^ 2 := hc.trans hu
  nlinarith [norm_nonneg (V i - V 0 - (τ i : ℂ) * (V m - V 0))]

/-- Crude growth of a polygon: `O(m / S)`. -/
lemma growth_poly_crude (V : ℕ → ℂ) {m : ℕ} (hS : 0 < plen V m)
    (hne : ∀ i < m, V i ≠ V (i + 1)) :
    GrowthBound (ConstrCov.wc m (pw V m) V).toMeasure (max 1 (2 * (1 / plen V m) * m)) 1 :=
  ConstrCov.growth_wc (by positivity) (fun i _ => div_nonneg (norm_nonneg _) hS.le)
    (by simp only [pw]; rw [← Finset.sum_div]; exact (div_self hS.ne').le) hne
    (fun i _ => le_of_eq (by simp only [pw, ell]; ring))

lemma proj_sub (x v p q : ℂ) :
    proj x v p - proj x v q = ((p - q) * (starRingEnd ℂ) v).re / ‖v‖ := by
  unfold proj
  rw [← sub_div, ← Complex.sub_re, ← sub_mul, show p - x - (q - x) = p - q by ring]

/-- **Forward-edge lemma**: if the excess `S - ρ` is at most a quarter of every edge, every
edge advances along the chord by at least `3/4` of its length. -/
lemma forward_of_excess (V : ℕ → ℂ) {m : ℕ} (hv : V m ≠ V 0)
    (hexc : ∀ i < m, plen V m - ‖V m - V 0‖ ≤ ell V i / 4) :
    ∀ i < m, 3 / 4 * ell V i ≤
      proj (V 0) (V m - V 0) (V (i + 1)) - proj (V 0) (V m - V 0) (V i) := by
  intro i hi
  set v := V m - V 0 with hvdef
  have hρ : 0 < ‖v‖ := norm_pos_iff.2 (sub_ne_zero.2 hv)
  set r : ℕ → ℝ := fun j => ((V (j + 1) - V j) * (starRingEnd ℂ) v).re with hr
  have hrle : ∀ j, r j ≤ ell V j * ‖v‖ := fun j => by
    calc r j ≤ |r j| := le_abs_self _
      _ ≤ ‖(V (j + 1) - V j) * (starRingEnd ℂ) v‖ := Complex.abs_re_le_norm _
      _ = ell V j * ‖v‖ := by rw [norm_mul, Complex.norm_conj]; rfl
  have hsum : ∑ j ∈ Finset.range m, r j = ‖v‖ ^ 2 := by
    simp only [hr]
    rw [← Complex.re_sum, ← Finset.sum_mul, Finset.sum_range_sub (fun j => V j) m,
      ← hvdef, Complex.mul_conj']
    norm_cast
  have hsingle : ell V i * ‖v‖ - r i ≤
      ∑ j ∈ Finset.range m, (ell V j * ‖v‖ - r j) :=
    Finset.single_le_sum (f := fun j => ell V j * ‖v‖ - r j)
      (fun j _ => sub_nonneg.2 (hrle j)) (Finset.mem_range.2 hi)
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum] at hsingle
  have hS : ∑ j ∈ Finset.range m, ell V j = plen V m := rfl
  rw [hS] at hsingle
  have h4 := hexc i hi
  rw [proj_sub, le_div_iff₀ hρ]
  show 3 / 4 * ell V i * ‖v‖ ≤ r i
  nlinarith

/-- Forward growth of a polygon: universal constant `8 / (3 S)`. -/
lemma growth_poly_forward (V : ℕ → ℂ) {m : ℕ} (hS : 0 < plen V m) (hv : V m ≠ V 0)
    (hpos : ∀ i < m, 0 < ell V i)
    (hexc : ∀ i < m, plen V m - ‖V m - V 0‖ ≤ ell V i / 4) (z : ℂ) (t : ℝ) :
    (ConstrCov.wc m (pw V m) V).toMeasure (Metric.ball z t) ≤
      ENNReal.ofReal (2 * (4 / (3 * plen V m)) * t) := by
  have hfwd := forward_of_excess V hv hexc
  refine forward_growth (V 0) (sub_ne_zero.2 hv) (by positivity)
    (fun i _ => div_nonneg (norm_nonneg _) hS.le) (fun i hi => ?_) (fun i hi => ?_) z t
  · have := hfwd i hi; have := hpos i hi; linarith
  · have := hfwd i hi
    show ell V i / plen V m ≤ _
    rw [div_le_iff₀ hS]
    have e : 4 / (3 * plen V m) * (proj (V 0) (V m - V 0) (V (i + 1)) -
        proj (V 0) (V m - V 0) (V i)) * plen V m =
        4 / 3 * (proj (V 0) (V m - V 0) (V (i + 1)) - proj (V 0) (V m - V 0) (V i)) := by
      field_simp
    rw [e]; linarith

/-! ## Small-excess configurations -/

/-- The small-excess configuration in vertex form: all hypotheses of Lemma 3.1 at scale `1`. -/
lemma small_index {M : ℕ} (hM : (16 : ℝ) ≤ M) {δ : ℝ} (hδ0 : 0 < δ) {k : ℕ} {V : ℕ → ℂ}
    {m : ℕ} (hm : 1 ≤ m) (hm3 : m ≤ 3 * M)
    (hρ1 : 31 / 32 ≤ ‖V m - V 0‖) (hρ2 : ‖V m - V 0‖ ≤ 33 / 32)
    (hℓ : ∀ i < m, ‖V m - V 0‖ / (2 * M) ≤ ell V i)
    (hA1 : (k : ℝ) * δ ^ 2 ≤ Real.log (plen V m / ‖V m - V 0‖))
    (hA2 : Real.log (plen V m / ‖V m - V 0‖) < ((k : ℝ) + 1) * δ ^ 2)
    (hA3 : Real.log (plen V m / ‖V m - V 0‖) ≤ 1) :
    (ConstrCov.wc m (pw V m) V).IsProb ∧
    GrowthBound (ConstrCov.segMeas (V 0) (V m)) (7 * gFactor M δ (1 / 32) k) 1 ∧
    GrowthBound (ConstrCov.wc m (pw V m) V).toMeasure (7 * gFactor M δ (1 / 32) k) 1 ∧
    CoupledWithin (ConstrCov.segMeas (V 0) (V m)) (ConstrCov.wc m (pw V m) V).toMeasure
      (6 * δ * √((k : ℝ) + 1)) := by
  set ρ := ‖V m - V 0‖ with hρdef
  set S := plen V m with hSdef
  set A := Real.log (S / ρ) with hAdef
  have hMpos : (0 : ℝ) < M := by linarith
  have hρ : 0 < ρ := by linarith
  have hv : V m ≠ V 0 := fun h => by
    rw [hρdef, h, sub_self, norm_zero] at hρ; exact lt_irrefl _ hρ
  have hℓpos : ∀ i < m, 0 < ell V i := fun i hi => lt_of_lt_of_le (by positivity) (hℓ i hi)
  have hS : 0 < S := Finset.sum_pos (fun i hi => hℓpos i (Finset.mem_range.1 hi))
    ⟨0, Finset.mem_range.2 (by omega)⟩
  have hSρ : ρ ≤ S := norm_sub_V0_le V m
  have hA0 : 0 ≤ A := le_trans (by positivity) hA1
  obtain ⟨hE1, hE2⟩ := excess_facts hρ hS hA0 hA3
  have hg1 : 1 ≤ gFactor M δ (1 / 32) k := by unfold gFactor; split_ifs <;> linarith
  refine ⟨isProb_poly V hS, ?_, ?_, ?_⟩
  · refine segMeas_growth (Ne.symm hv) (by linarith) ?_
    nlinarith
  · unfold gFactor
    split_ifs with hg
    · have hAsmall : A ≤ 1 / (32 * M) := by
        calc A ≤ ((k : ℝ) + 1) * δ ^ 2 := hA2.le
          _ = δ ^ 2 * ((k : ℝ) + 1) := by ring
          _ ≤ 1 / 32 / M := hg
          _ = 1 / (32 * M) := by rw [div_div]
      have hexc : ∀ i < m, S - ρ ≤ ell V i / 4 := by
        intro i hi
        have h1 := hℓ i hi
        have h2 : 4 * ρ * A ≤ 4 * ρ * (1 / (32 * M)) := by gcongr
        have h3 : 4 * ρ * (1 / (32 * M)) = ρ / (2 * M) / 4 := by ring
        linarith
      refine growth_of_le (by norm_num) (fun z t _ => toMeasure_le_one (isProb_poly V hS) _)
        (fun z t ht => ?_)
      refine (growth_poly_forward V hS hv hℓpos hexc z t).trans (ENNReal.ofReal_le_ofReal ?_)
      have h7 : 2 * (4 / (3 * S)) ≤ 7 := by
        rw [show 2 * (4 / (3 * S)) = 8 / (3 * S) by ring, div_le_iff₀ (by positivity)]
        linarith
      calc 2 * (4 / (3 * S)) * t ≤ 7 * t := mul_le_mul_of_nonneg_right h7 ht.le
        _ = 7 * 1 * t := by ring
    · refine growth_mono zero_le_one (growth_poly_crude V hS (fun i hi h => ?_)) ?_
      · have := hℓpos i hi
        rw [ell, ← h, sub_self, norm_zero] at this
        exact lt_irrefl _ this
      · refine max_le (by linarith) ?_
        have hm3' : (m : ℝ) ≤ 3 * M := by exact_mod_cast hm3
        rw [show 2 * (1 / S) * (m : ℝ) = 2 * m / S by ring, div_le_iff₀ hS]
        nlinarith
  · refine coupled_poly V hS (by positivity) ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    have hρsq : ρ ^ 2 ≤ (33 / 32) ^ 2 := by nlinarith
    have hAk : A ≤ ((k : ℝ) + 1) * δ ^ 2 := hA2.le
    have := mul_le_mul hρsq hAk hA0 (by positivity)
    nlinarith

lemma cellRad_mul_le {M : ℕ} (hM : (16 : ℝ) ≤ M) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    cellRad M * δ ≤ 1 / 64 := by
  have hM2 : (0 : ℝ) < (M : ℝ) ^ 2 := pow_pos (by linarith) 2
  have h1 : cellRad M ≤ 1 / 64 := by
    unfold cellRad
    rw [div_le_iff₀ hM2]
    nlinarith
  have h0 : 0 ≤ cellRad M := by unfold cellRad; positivity
  nlinarith

lemma rho_bounds {M : ℕ} (hM : (16 : ℝ) ≤ M) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {x y : ℂ}
    (hx : ‖x‖ ≤ cellRad M * δ) (hy : ‖y - 1‖ ≤ cellRad M * δ) :
    31 / 32 ≤ ‖y - x‖ ∧ ‖y - x‖ ≤ 33 / 32 := by
  have hc := cellRad_mul_le hM hδ0 hδ1
  have h := abs_norm_sub_norm_le (y - x) 1
  rw [norm_one, show y - x - 1 = (y - 1) - x by ring] at h
  have h2 := norm_sub_le (y - 1) x
  have h3 := abs_le.1 (h.trans h2)
  constructor <;> linarith [h3.1, h3.2]

lemma polyComb_pair {x y : ℂ} (hxy : x ≠ y) : polyComb [x, y] = [((1 : ℝ), x, y)] := by
  have h : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
  simp [polyComb, polyLen, edges, h]

lemma isProb_single (a b : ℂ) : SegComb.IsProb [((1 : ℝ), a, b)] :=
  ⟨by simp, by simp [SegComb.mass]⟩

/-- **Small-excess configurations** satisfy the hypotheses of Lemma 3.1. -/
lemma small_good {M : ℕ} (hM : (16 : ℝ) ≤ M) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {k : ℕ}
    {c : Config} (hc : c ∈ smallFamily M δ k) :
    CfgGood (7 * gFactor M δ (1 / 32) k) 1 (6 * δ * √((k : ℝ) + 1)) c := by
  obtain ⟨x, y, z, rfl, hhead, hlast, hx, hy, hlen2, hlen3, hdrop, hlastE, hA1, hA2, hA3⟩ := hc
  set m := z.length - 1 with hmdef
  set V : ℕ → ℂ := fun i => z.getD i 0 with hVdef
  have hlen : z.length = m + 1 := by omega
  have hz : z = (List.range (m + 1)).map V := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      simp [V, List.getD_eq_getElem?_getD, h1]
  have hV0 : V 0 = x := by
    rw [hz, List.head?_map, List.head?_range] at hhead
    simpa using hhead
  have hVm : V m = y := by
    rw [hz, List.getLast?_map, List.getLast?_range] at hlast
    simpa using hlast
  have hedges : edges z = (List.range m).map (fun i => (V i, V (i + 1))) := by
    rw [hz]; exact LFPPRecords.edges_range_map V m
  have hpoly : polyLen z = plen V m := by rw [hz, LFPPRecords.polyLen_range_map]; rfl
  have hcomb : polyComb z = ConstrCov.wc m (pw V m) V := by
    unfold polyComb; rw [hedges, hpoly, List.map_map]; rfl
  obtain ⟨hρ1, hρ2⟩ := rho_bounds hM hδ0.le hδ1.le hx hy
  have hm1 : 1 ≤ m := by omega
  have hm3 : m ≤ 3 * M := by omega
  rw [hpoly] at hA1 hA2 hA3
  rw [hedges] at hdrop hlastE
  subst hV0 hVm
  have hMpos : (0 : ℝ) < M := by linarith
  have hℓ : ∀ i < m, ‖V m - V 0‖ / (2 * M) ≤ ell V i := by
    obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hsplit : (List.range m).map (fun i => (V i, V (i + 1))) =
        (List.range m').map (fun i => (V i, V (i + 1))) ++ [(V m', V (m' + 1))] := by
      rw [hm', List.range_succ, List.map_append]; rfl
    rw [hsplit, List.dropLast_concat] at hdrop
    rw [hsplit, List.getLast?_concat] at hlastE
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 (hm' ▸ hi) with hi' | rfl
    · have := hdrop (V i, V (i + 1)) (List.mem_map.2 ⟨i, List.mem_range.2 hi', rfl⟩)
      rw [ell]
      simp only at this
      rw [this]
      have hρ0 : 0 ≤ ‖V m - V 0‖ := norm_nonneg _
      rw [div_le_div_iff₀ (by positivity) hMpos]
      nlinarith
    · have := (hlastE (V i, V (i + 1)) rfl).1
      rw [ell, ← hm']
      simpa [hm'] using this
  obtain ⟨h1, h2, h3, h4⟩ := small_index hM hδ0 hm1 hm3 hρ1 hρ2 hℓ hA1 hA2 hA3
  have hv : V 0 ≠ V m := fun h => by
    rw [h, sub_self, norm_zero] at hρ1; norm_num at hρ1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [polyComb_pair hv]; exact isProb_single _ _
  · rw [hcomb]; exact h1
  · rw [polyComb_pair hv, toMeasure_single]; exact h2
  · rw [hcomb]; exact h3
  · rw [polyComb_pair hv, toMeasure_single, hcomb]; exact h4

/-! ## Large-excess configurations -/

lemma one_lt_of_floor {δ : ℝ} (hδ0 : 0 < δ) {k : ℕ} (hk : k = ⌊δ ^ (-2 : ℤ)⌋₊) :
    1 < δ ^ 2 * ((k : ℝ) + 1) := by
  have h := Nat.lt_floor_add_one (δ ^ (-2 : ℤ))
  rw [← hk] at h
  have e : δ ^ (-2 : ℤ) = (δ ^ 2)⁻¹ := by rw [zpow_neg, zpow_two, sq]
  rw [e] at h
  have hd2 : 0 < δ ^ 2 := by positivity
  calc (1 : ℝ) = δ ^ 2 * (δ ^ 2)⁻¹ := (mul_inv_cancel₀ hd2.ne').symm
    _ < δ ^ 2 * ((k : ℝ) + 1) := mul_lt_mul_of_pos_left h hd2

/-- **Large-excess configurations** satisfy the hypotheses of Lemma 3.1. -/
lemma large_good {M : ℕ} (hM : (16 : ℝ) ≤ M) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {k : ℕ}
    (hk : k = ⌊δ ^ (-2 : ℤ)⌋₊) {c : Config} (hc : c ∈ largeFamily M δ) :
    CfgGood (7 * gFactor M δ (1 / 32) k) 1 (6 * δ * √((k : ℝ) + 1)) c := by
  obtain ⟨x, y, x', y', rfl, hx, hy, hx', hy', hl1, hl2⟩ := hc
  obtain ⟨hρ1, hρ2⟩ := rho_bounds hM hδ0.le hδ1.le hx hy
  have hMpos : (0 : ℝ) < M := by linarith
  have hk1 := one_lt_of_floor hδ0 hk
  have hg : gFactor M δ (1 / 32) k = M := by
    unfold gFactor
    split_ifs with h
    · have : (1 : ℝ) / 32 / M ≤ 1 := by rw [div_le_one hMpos]; linarith
      linarith
    · rfl
  have hu : 1 ≤ δ * √((k : ℝ) + 1) := by
    have : 1 ≤ √(δ ^ 2 * ((k : ℝ) + 1)) := Real.one_le_sqrt.2 hk1.le
    rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hδ0.le] at this
  have hxy : x ≠ y := fun h => by
    rw [h, sub_self, norm_zero] at hρ1; norm_num at hρ1
  have hl0 : 0 < ‖y' - x'‖ := lt_of_lt_of_le (by positivity) hl1
  have hxy' : x' ≠ y' := fun h => by
    rw [h, sub_self, norm_zero] at hl0; exact lt_irrefl _ hl0
  rw [hg]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [polyComb_pair hxy]; exact isProb_single _ _
  · rw [polyComb_pair hxy']; exact isProb_single _ _
  · rw [polyComb_pair hxy, toMeasure_single]
    exact segMeas_growth hxy (by linarith) (by nlinarith)
  · rw [polyComb_pair hxy', toMeasure_single]
    refine segMeas_growth hxy' (by linarith) ?_
    have h1 := mul_le_mul_of_nonneg_left hl1 (by positivity : (0 : ℝ) ≤ 7 * M)
    have h2 : 7 * (M : ℝ) * (‖y - x‖ / (2 * M)) = 7 / 2 * ‖y - x‖ := by
      field_simp
    linarith
  · rw [polyComb_pair hxy, polyComb_pair hxy', toMeasure_single, toMeasure_single]
    refine coupled_seg ?_ ?_
    · rw [norm_sub_rev]; nlinarith
    · have := norm_sub_le (y - x) (y' - x)
      rw [show y - x - (y' - x) = y - y' by ring] at this
      nlinarith

/-- **Every normalized local configuration** satisfies the hypotheses of Lemma 3.1 with growth
constant `7 g` at scale `1` and coupling distance `6 δ √(k+1)`. -/
lemma local_good {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {large : Bool}
    {k : ℕ} (hk : large = true → k = ⌊δ ^ (-2 : ℤ)⌋₊) {c : Config}
    (hc : c ∈ localFamily (16 ^ n) δ large k) :
    CfgGood (7 * gFactor (16 ^ n) δ (1 / 32) k) 1 (6 * δ * √((k : ℝ) + 1)) c := by
  have hM : (16 : ℝ) ≤ ((16 ^ n : ℕ) : ℝ) := by
    push_cast; exact le_self_pow₀ (by norm_num) (by omega)
  cases large with
  | true =>
    simp only [localFamily, ite_true] at hc
    exact large_good hM hδ0 hδ1 (hk rfl) hc
  | false =>
    simp only [localFamily, Bool.false_eq_true, ite_false] at hc
    exact small_good hM hδ0 hδ1 hc

/-- `CfgGood` is transported by similarities (the scale and the coupling distance are
multiplied by `|α|`). -/
lemma cfgGood_cfgMap {L R u : ℝ} {s : ℂ × ℂ} (hs : s.1 ≠ 0) {c : Config}
    (h : CfgGood L R u c) : CfgGood L (‖s.1‖ * R) (‖s.1‖ * u) (cfgMap s c) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  dsimp only [CfgGood, cfgMap]
  rw [polyComb_map s hs, polyComb_map s hs, toMeasure_image_simMap, toMeasure_image_simMap]
  exact ⟨isProb_image _ h1, isProb_image _ h2, growthBound_map_simMap hs h3,
    growthBound_map_simMap hs h4, coupledWithin_map_simMap s h5⟩

end LQGDimension.RecVar
