/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P8FullPath at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P8Discretize
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P7SupBound
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.InputsFullPath
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistFieldOsc

 















set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos.P8

open P7

 
def boxV : Set ℂ := Complex.re ⁻¹' Icc (-(4 / 5)) (4 / 5) ∩ Complex.im ⁻¹' Icc (-(4 / 5)) (4 / 5)

lemma convex_boxV : Convex ℝ boxV :=
  ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

lemma isBounded_boxV : Bornology.IsBounded boxV := by
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset fun x hx => ?_
  simp only [Metric.mem_closedBall, dist_zero_right]
  have h1 := abs_le.mpr hx.1
  have h2 := abs_le.mpr hx.2
  linarith [Complex.norm_le_abs_re_add_abs_im x]

 
lemma crossLen_pos_lt_top {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) :
    0 < crossLenIn ξ φ upperAnnulus upperAnnulusInner upperAnnulusOuter ∧
      crossLenIn ξ φ upperAnnulus upperAnnulusInner upperAnnulusOuter < ⊤ := by
  constructor
  · obtain ⟨M, hM⟩ := upperAnnulus_isCompact.exists_bound_of_continuousOn hφ.continuousOn
    have hlow : ENNReal.ofReal (Real.exp (-(|ξ| * M)) * (3 / 10)) ≤
        crossLenIn ξ φ upperAnnulus upperAnnulusInner upperAnnulusOuter := by
      refine le_crossLenIn fun P hP => ?_
      obtain ⟨z, hz, w, hw, hPc, hU⟩ := hP
      refine le_trans ?_ (lfppLen_ge hPc fun t ht => by
        have := hM (P t) (hU t ht); rwa [Real.norm_eq_abs] at this)
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
      have h1 := squareRadius_le_norm_add w z
      have hw' : squareRadius w = 3 / 4 := hw
      have hz' : squareRadius z = 9 / 20 := hz
      rw [hw', hz'] at h1
      linarith
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hlow
  · obtain ⟨M, hM⟩ := eastCorridor.isCompact_toSet.exists_bound_of_continuousOn hφ.continuousOn
    refine lt_of_le_of_lt (upperAnnulus_crossLen_le_eastCorridor ξ φ) ?_
    refine lt_of_le_of_lt (rectLen_le eastCorridor (by norm_num [eastCorridor])
      (by norm_num [eastCorridor]) (M := M) fun x hx => ?_) ENNReal.ofReal_lt_top
    have := hM x hx; rwa [Real.norm_eq_abs] at this

 
theorem full_path_of_good {n : ℕ} (hn : 5 ≤ n) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (h : EuclideanSpace ℝ (DGFFSite n)) {φ : ℂ → ℝ} (hφ : Continuous φ) {Δ θ δ : ℝ}
    (hfield : ∀ u : DGFFSite n, |(u.1.1 : ℝ)| ≤ 4 / 5 * Nn n → |(u.1.2 : ℝ)| ≤ 4 / 5 * Nn n →
      h u ≤ φ (siteZ n u) + Δ)
    (hosc : ∀ x y : ℂ, |x.re| ≤ 4 / 5 → |x.im| ≤ 4 / 5 → |y.re| ≤ 4 / 5 → |y.im| ≤ 4 / 5 →
      ‖x - y‖ ≤ 3 / Nn n → φ x ≤ φ y + θ)
    (hconst : 128 * (Nn n : ℝ) * Real.exp (ξ * (Δ + θ)) ≤ (2 : ℝ) ^ ((1 + δ) * (n : ℝ))) :
    ∃ (N : ℕ) (p : ℕ → DGFFSite n),
      latticeRadius (p 0).1 ≤ dgffInnerRadius n ∧
      dgffOuterRadius n ≤ latticeRadius (p N).1 ∧
      (∀ i < N, latticeAdjacent (p i).1 (p (i + 1)).1) ∧
      dgffPathCost n ξ h (List.ofFn fun i : Fin (N + 1) => p i) ≤
        (2 : ℝ) ^ ((1 + δ) * (n : ℝ)) *
          (crossLenIn ξ φ upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal := by
  set L := crossLenIn ξ φ upperAnnulus upperAnnulusInner upperAnnulusOuter with hLdef
  obtain ⟨hL0, hLt⟩ := crossLen_pos_lt_top (ξ := ξ) hφ
  have hL2 : L < 2 * L := by
    rw [two_mul]; exact ENNReal.lt_add_right hLt.ne hL0.ne'
  have hL2' : (⨅ P ∈ {P | AdmPath upperAnnulus upperAnnulusInner upperAnnulusOuter P},
      lfppLen ξ φ P) < 2 * L := by
    rw [← crossLenIn_eq_biInf]; exact hL2
  obtain ⟨P, hPlt'⟩ := iInf_lt_iff.mp hL2'
  obtain ⟨hP, hPlt⟩ := iInf_lt_iff.mp hPlt'
  obtain ⟨M, p, h0, h1, h2, h3⟩ := lattice_path_of_admPath hn hξ h φ hfield hosc hP
  refine ⟨M, p, h0, h1, h2, ?_⟩
  have hcost0 : 0 ≤ dgffPathCost n ξ h (List.ofFn fun i : Fin (M + 1) => p i) :=
    inclusivePathCost_nonneg _ (fun _ => (Real.exp_pos _).le) _
  have hmain : ENNReal.ofReal (dgffPathCost n ξ h (List.ofFn fun i : Fin (M + 1) => p i)) ≤
      ENNReal.ofReal (128 * Nn n * Real.exp (ξ * (Δ + θ)) * L.toReal) := by
    refine h3.trans ?_
    calc ENNReal.ofReal (64 * Nn n * Real.exp (ξ * (Δ + θ))) * lfppLen ξ φ P
        ≤ ENNReal.ofReal (64 * Nn n * Real.exp (ξ * (Δ + θ))) * (2 * L) := by gcongr
      _ = ENNReal.ofReal (128 * Nn n * Real.exp (ξ * (Δ + θ)) * L.toReal) := by
          have hLr : ENNReal.ofReal L.toReal = L := ENNReal.ofReal_toReal hLt.ne
          have e1 : (128 : ℝ) * Nn n * Real.exp (ξ * (Δ + θ)) * L.toReal =
              (64 * Nn n * Real.exp (ξ * (Δ + θ))) * (2 * L.toReal) := by ring
          rw [e1, ENNReal.ofReal_mul (show (0 : ℝ) ≤ 64 * Nn n * Real.exp (ξ * (Δ + θ)) by
            positivity), ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num), hLr]
          simp
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hmain
  refine hreal.trans ?_
  exact mul_le_mul_of_nonneg_right hconst ENNReal.toReal_nonneg

 
theorem dgffWhiteNoiseFullPathComparison_proved : Inputs.DGFFWhiteNoiseFullPathComparison := by
  intro ξ Ω _ P W hW
  haveI := hW.isProbabilityMeasure
  refine ⟨fun n => dgffCoupling n P W, fun n => dgffCoupling_isProbability n hW,
    fun n => dgffCoupling_fst n hW, fun n => dgffCoupling_snd n hW, ?_⟩
  intro δ hδ
  have hξ : (0 : ℝ) < ξ := ξ.2
  set δ' : ℝ := δ * Real.log 2 / (4 * ξ) with hδ'
  have hδ'0 : 0 < δ' := by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  
  set bad1 : ℕ → Set Ω := fun n => {ω | ∃ v : DGFFSite n, |(v.1.1 : ℝ)| ≤ 4 / 5 * Nn n ∧
    |(v.1.2 : ℝ)| ≤ 4 / 5 * Nn n ∧ δ' * n < |W (fKerL2 n v) ω - phiMN W P 0 n (siteZ n v) ω|}
  obtain ⟨C, σ2, hC, hσ2, hosc⟩ := DG20Pt.pt_dist_field_osc_tail boxV isBounded_boxV convex_boxV 3
    (by norm_num)
  set bad2 : ℕ → Set Ω := fun n => {ω | ∃ z ∈ boxV, ∃ w ∈ boxV,
    dist z w ≤ 3 * ((2 : ℝ) ^ n)⁻¹ ∧ 3 * (δ' * n / 3) < |phiMN W P 0 n z ω - phiMN W P 0 n w ω|}
  have hb1 : Tendsto (fun n => P (bad1 n)) atTop (𝓝 0) := tendsto_dgff_phi_sup hW hδ'0
  have hb2 : Tendsto (fun n => P (bad2 n)) atTop (𝓝 0) := by
    set a := δ' ^ 2 / (18 * σ2)
    have ha : 0 < a := by positivity
    have hle : ∀ n : ℕ, P (bad2 n) ≤
        ENNReal.ofReal (C * ((4 : ℝ) ^ (n + 1) * Real.exp (-a * (n : ℝ) ^ 2))) := by
      intro n
      have h := hosc hW n (δ' * n / 3) (by positivity)
      rw [← ofReal_measureReal (measure_ne_top _ _)]
      refine ENNReal.ofReal_le_ofReal (h.trans ?_)
      have he : Real.exp (-(δ' * n / 3) ^ 2 / (2 * σ2)) = Real.exp (-a * (n : ℝ) ^ 2) := by
        congr 1; simp only [a]; field_simp; ring
      rw [he, pow_succ (4 : ℝ) n]
      have : 0 ≤ C * 4 ^ n * Real.exp (-a * (n : ℝ) ^ 2) := by positivity
      have e4 : C * ((4 : ℝ) ^ n * 4 * Real.exp (-a * (n : ℝ) ^ 2)) =
          4 * (C * 4 ^ n * Real.exp (-a * (n : ℝ) ^ 2)) := by ring
      linarith
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (C * ((4 : ℝ) ^ (n + 1) *
        Real.exp (-a * (n : ℝ) ^ 2)))) atTop (𝓝 0) := by
      have := (tendsto_pow_four_mul_exp ha).const_mul C
      rw [mul_zero] at this
      have h := ENNReal.tendsto_ofReal this
      rwa [ENNReal.ofReal_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun n => zero_le) (Eventually.of_forall hle)
  
  have hgood : ∀ᶠ n : ℕ in atTop, ∀ ω, ω ∉ bad1 n → ω ∉ bad2 n →
      (dgffVec n W ω, ω) ∈ {v : EuclideanSpace ℝ (DGFFSite n) × Ω |
        ∃ (N : ℕ) (p : ℕ → DGFFSite n),
          latticeRadius (p 0).1 ≤ dgffInnerRadius n ∧
          dgffOuterRadius n ≤ latticeRadius (p N).1 ∧
          (∀ i < N, latticeAdjacent (p i).1 (p (i + 1)).1) ∧
          dgffPathCost n (ξ : ℝ) v.1 (List.ofFn fun i : Fin (N + 1) => p i) ≤
            (2 : ℝ) ^ ((1 + δ) * (n : ℝ)) *
              (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x v.2)
                upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal} := by
    filter_upwards [eventually_ge_atTop 5, eventually_ge_atTop ⌈14 / δ⌉₊] with n hn5 hn14
    intro ω h1 h2
    have hcont : Continuous fun x => phiMN W P 0 n x ω :=
      (isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω
    have hNn : (Nn n : ℝ) = (2 : ℝ) ^ n := by simp [Nn]
    refine full_path_of_good hn5 hξ.le (dgffVec n W ω) hcont (Δ := δ' * n) (θ := δ' * n)
      ?_ ?_ ?_
    · intro u hu1 hu2
      have : ¬ (δ' * n < |W (fKerL2 n u) ω - phiMN W P 0 n (siteZ n u) ω|) := fun hlt =>
        h1 ⟨u, hu1, hu2, hlt⟩
      push_neg at this
      have := (abs_le.mp this).2
      show W (fKerL2 n u) ω ≤ _
      linarith
    · intro x y hx1 hx2 hy1 hy2 hxy
      have hx : x ∈ boxV := ⟨abs_le.mp hx1, abs_le.mp hx2⟩
      have hy : y ∈ boxV := ⟨abs_le.mp hy1, abs_le.mp hy2⟩
      have hd : dist x y ≤ 3 * ((2 : ℝ) ^ n)⁻¹ := by
        rw [Complex.dist_eq, ← div_eq_mul_inv, ← hNn]; exact hxy
      have : ¬ (3 * (δ' * n / 3) < |phiMN W P 0 n x ω - phiMN W P 0 n y ω|) := fun hlt =>
        h2 ⟨x, hx, y, hy, hd, hlt⟩
      push_neg at this
      have := (abs_le.mp this).2
      linarith
    · 
      have hn14' : 14 / δ ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn14)
      have hδn : 14 ≤ δ * n := by rw [div_le_iff₀ hδ] at hn14'; linarith
      have hexp : Real.exp ((ξ : ℝ) * (δ' * n + δ' * n)) = (2 : ℝ) ^ (δ * n / 2) := by
        rw [Real.rpow_def_of_pos (by norm_num)]
        congr 1; simp only [hδ']; field_simp; ring
      have h2pow : (2 : ℝ) ^ ((1 + δ) * (n : ℝ)) = (Nn n : ℝ) * (2 : ℝ) ^ (δ * n / 2) *
          (2 : ℝ) ^ (δ * n / 2) := by
        rw [hNn, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
        congr 1; ring
      rw [hexp, h2pow]
      have h128 : (128 : ℝ) ≤ (2 : ℝ) ^ (δ * n / 2) := by
        have : (128 : ℝ) = (2 : ℝ) ^ (7 : ℝ) := by norm_num
        rw [this]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have hpos : 0 < (Nn n : ℝ) * (2 : ℝ) ^ (δ * n / 2) := by positivity
      nlinarith
  
  have hlow : ∀ᶠ n : ℕ in atTop, 1 - (P (bad1 n) + P (bad2 n)) ≤ dgffCoupling n P W
      {v : EuclideanSpace ℝ (DGFFSite n) × Ω |
        ∃ (N : ℕ) (p : ℕ → DGFFSite n),
          latticeRadius (p 0).1 ≤ dgffInnerRadius n ∧
          dgffOuterRadius n ≤ latticeRadius (p N).1 ∧
          (∀ i < N, latticeAdjacent (p i).1 (p (i + 1)).1) ∧
          dgffPathCost n (ξ : ℝ) v.1 (List.ofFn fun i : Fin (N + 1) => p i) ≤
            (2 : ℝ) ^ ((1 + δ) * (n : ℝ)) *
              (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x v.2)
                upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal} := by
    filter_upwards [hgood] with n hn
    set E := {v : EuclideanSpace ℝ (DGFFSite n) × Ω |
        ∃ (N : ℕ) (p : ℕ → DGFFSite n),
          latticeRadius (p 0).1 ≤ dgffInnerRadius n ∧
          dgffOuterRadius n ≤ latticeRadius (p N).1 ∧
          (∀ i < N, latticeAdjacent (p i).1 (p (i + 1)).1) ∧
          dgffPathCost n (ξ : ℝ) v.1 (List.ofFn fun i : Fin (N + 1) => p i) ≤
            (2 : ℝ) ^ ((1 + δ) * (n : ℝ)) *
              (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x v.2)
                upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal}
    set g : Ω → EuclideanSpace ℝ (DGFFSite n) × Ω := fun ω => (dgffVec n W ω, ω)
    have hg : AEMeasurable g P := ((measurable_dgffVec n hW).prodMk measurable_id).aemeasurable
    have hsub : (bad1 n ∪ bad2 n)ᶜ ⊆ g ⁻¹' E := by
      intro ω hω
      simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hω
      exact hn ω hω.1 hω.2
    have h1 : P univ ≤ P (g ⁻¹' E) + P ((g ⁻¹' E)ᶜ) := by
      rw [← Set.union_compl_self (g ⁻¹' E)]; exact measure_union_le _ _
    have h2 : P ((g ⁻¹' E)ᶜ) ≤ P (bad1 n) + P (bad2 n) := by
      refine (measure_mono ?_).trans (measure_union_le _ _)
      intro ω hω
      by_contra hcon
      exact hω (hsub hcon)
    rw [measure_univ] at h1
    have h3 : 1 - (P (bad1 n) + P (bad2 n)) ≤ P (g ⁻¹' E) := by
      rw [tsub_le_iff_right]; exact h1.trans (add_le_add le_rfl h2)
    exact h3.trans (Measure.le_map_apply hg E)
  have hlim : Tendsto (fun n => 1 - (P (bad1 n) + P (bad2 n))) atTop (𝓝 1) := by
    have h := ENNReal.Tendsto.sub tendsto_const_nhds (hb1.add hb2) (Or.inl ENNReal.one_ne_top)
    simpa using h
  haveI : ∀ n, IsProbabilityMeasure (dgffCoupling n P W) := fun n => dgffCoupling_isProbability n hW
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds hlow
    (Eventually.of_forall fun n => prob_le_one)

end SupercriticalLQGUniqueness.B2.QPos.P8
