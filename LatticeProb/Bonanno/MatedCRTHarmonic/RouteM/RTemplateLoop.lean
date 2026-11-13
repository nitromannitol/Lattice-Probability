/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.RTemplateLoop at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.RWalks

/-!
# Route M,: the closed sub-walk of Lemma D″ winds once

Let `v j = v k` with `j`
in the radial block and `k` in the final block of a template walk (Lemma R). The closed walk `v j → ⋯ → v k`
(`exists_templateLoop`):

* has its drawn loop in the annulus `22r/25 < |· - z| < 28r/25` (every cell of the walk is within `r/60` of the
  template, whose radius is in `[0.9r, 1.1r]`);
* has winding number one about `z`.

TF3 §9 obtains the degree from the sealed `loopDeg_eq_one_of_near_polarTemplate` through a paused parametrization;
here it is computed dart by dart, which avoids reparametrizing TFJ's drawn loop. For the dart `(v i, v (i+1))`
put `T_i := T(α (i+1))`, a template point within `1/60` (normalized) of both end cells (by the overlap condition), with
template angle `Θ_i = polarAngle (4 α (i+1))`. TFJ's sector rule with reference direction `T_i` gives the dart
increment `ℓ⁺_i - ℓ⁻_i`, where `ℓ⁻_i = log (P_i / T_i) + log T_i` and `ℓ⁺_i = log (P_{i+1} / T_i) + log T_i` are
logarithms of the normalized vertex points `P_i`, `P_{i+1}` (with `log T_i := log |T_i| + iΘ_i`). Consecutive
logarithms of the same point agree, `ℓ⁺_i = ℓ⁻_{i+1}`, because their imaginary parts differ by less than
`π/2 + π/2 + 7 · 4/50 < 2π` (the template angle is `7`-Lipschitz and the intervals have length `≤ 1/50`). So the
increments telescope to `ℓ⁺_{k-1} - ℓ⁻_j`, two logarithms of `P_k = P_j` whose imaginary parts differ by
`Θ_{k-1} - Θ_j ± π ∈ (π - 1/10, 3π + 1/10)` (`Θ_j = 0` on the radial piece, `Θ_{k-1} ∈ [2π - 1/10, 2π + 1/10]` on the
final piece): the total is `2πi`.
-/

set_option autoImplicit false

noncomputable section

open Set SimpleGraph SimpleGraph.Walk
open MatedCRTHarmonic.Topology QuantumZipper.CA.Topo

namespace MatedCRTHarmonic.RouteM

variable {V E : Type*} {G : LFMultigraph V E} {o : V} {H : CellularEmbedding G o}

/-- A point within `1/60` of a point of modulus `≥ 9/10` has a quotient with positive real part. -/
theorem re_div_pos_of_near {P T : ℂ} (hT : 9 / 10 ≤ ‖T‖) (h : ‖P - T‖ < 1 / 60) : 0 < (P / T).re := by
  have hTpos : 0 < ‖T‖ := by linarith
  have hT0 : T ≠ 0 := norm_pos_iff.mp hTpos
  have hq : P / T = 1 + (P - T) / T := by field_simp; ring
  have hn : ‖(P - T) / T‖ < 1 / 2 := by
    rw [norm_div, div_lt_iff₀ hTpos]
    linarith
  have hre := Complex.abs_re_le_norm ((P - T) / T)
  rw [hq, Complex.add_re, Complex.one_re]
  linarith [(abs_le.1 hre).1]

theorem abs_arg_div_lt_of_near {P T : ℂ} (hT : 9 / 10 ≤ ‖T‖) (h : ‖P - T‖ < 1 / 60) :
    |Complex.arg (P / T)| < Real.pi / 2 :=
  Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (re_div_pos_of_near hT h))

/-- **The closed sub-walk of Lemma D″** (TF3 §9 steps 1–2): if `v j = v k` with `β j ≤ 1/2` (e.g. `j` in the radial
block) and `α k ≥ 3/4` (`k` in the final block), `j < k`, the closed walk `v j → ⋯ → v k` has drawn loop in the annulus `22r/25 < |· - z| < 28r/25` and degree one
about `z`; its vertices are the `v i`, `j ≤ i ≤ k`. -/
theorem exists_templateLoop (D : H.MonotoneDrawing) {z : ℂ} {r ϑ : ℝ} (hr : 0 < r) {n : ℕ} {v : ℕ → V}
    {α β : ℕ → ℝ} (hW : IsTemplateWalk H z r ϑ n v α β) {j k : ℕ} (hjk : j < k) (hkn : k ≤ n)
    (hj2 : β j ≤ 1 / 2) (hk : 3 / 4 ≤ α k) (hv : v j = v k) :
    ∃ W : G.adj.Walk (v j) (v j),
      (∀ t, 22 * r / 25 < ‖drawnLoop D W t - z‖ ∧ ‖drawnLoop D W t - z‖ < 28 * r / 25) ∧
      (∃ hne : ∀ t, (drawnLoop D W - ContinuousMap.const unitInterval z) t ≠ 0,
        loopDeg (drawnLoop D W - ContinuousMap.const unitInterval z) hne ≠ 0) ∧
      (∀ y ∈ W.support, ∃ i, j ≤ i ∧ i ≤ k ∧ y = v i) := by
  have hpi := Real.pi_gt_three
  have hlen : j + (k - j) ≤ n := by omega
  set W : G.adj.Walk (v j) (v j) := (walkAlongSeq v hW.adj (k - j) j hlen).copy rfl
    ((congrArg v (show j + (k - j) = k by omega)).trans hv.symm) with hWdef
  have hWsupp : ∀ y ∈ W.support, ∃ i, j ≤ i ∧ i ≤ k ∧ y = v i := by
    intro y hy
    rw [hWdef, support_copy] at hy
    obtain ⟨t, ht, rfl⟩ := mem_support_walkAlongSeq v hW.adj (k - j) j hlen hy
    exact ⟨j + t, by omega, by omega, rfl⟩
  -- annulus
  have hann : ∀ t, 22 * r / 25 < ‖drawnLoop D W t - z‖ ∧ ‖drawnLoop D W t - z‖ < 28 * r / 25 := by
    refine drawnLoop_mem_of_forall_cell D W (fun q => 22 * r / 25 < ‖q - z‖ ∧ ‖q - z‖ < 28 * r / 25) ?_
    intro x hx q hq
    obtain ⟨i, -, hik, rfl⟩ := hWsupp x hx
    obtain ⟨h1, h2⟩ := hW.coord_annulus hr (hik.trans hkn) hq
    have hqz : ‖q - z‖ = r * ‖tmplCoord z r ϑ q‖ := by
      rw [norm_tmplCoord hr]
      field_simp
    rw [hqz]
    constructor <;> nlinarith
  have hne : ∀ t, (drawnLoop D W - ContinuousMap.const unitInterval z) t ≠ 0 := by
    intro t ht
    have h := (hann t).1
    simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply] at ht
    rw [ht, norm_zero] at h
    linarith
  -- the per-dart data
  set P : ℕ → ℂ := fun i => tmplCoord z r ϑ (D.Ψ (D.pt (v i))) with hP
  set T : ℕ → ℂ := fun i => tmplPt (α (i + 1)) with hT
  set Θ : ℕ → ℝ := fun i => polarAngle (4 * α (i + 1)) with hΘ
  set K : ℕ → ℂ := fun i => (Real.log (polarRadius (4 * α (i + 1))) : ℂ) + (Θ i : ℂ) * Complex.I with hK
  set ℓm : ℕ → ℂ := fun i => Complex.log (P i / T i) + K i with hℓm
  set ℓp : ℕ → ℂ := fun i => Complex.log (P (i + 1) / T i) + K i with hℓp
  -- facts on the dart range `j ≤ i < k`
  have hαI : ∀ i, i < k → 0 ≤ α (i + 1) ∧ α (i + 1) ≤ 1 := fun i hi => by
    obtain ⟨h0, h1, h2, -⟩ := hW.bounds (i + 1) (by omega)
    exact ⟨h0, h1.trans h2⟩
  have hTnorm : ∀ i, i < k → 9 / 10 ≤ ‖T i‖ := fun i hi => by
    obtain ⟨h0, h1⟩ := hαI i hi
    simp only [hT]
    rw [norm_tmplPt_of_mem h0 h1]
    exact (polarRadius_four_mul_bounds h0 h1).1
  have hT0 : ∀ i, i < k → T i ≠ 0 := fun i hi h0 => by
    have := hTnorm i hi
    rw [h0, norm_zero] at this
    linarith
  have hKexp : ∀ i, i < k → Complex.exp (K i) = T i := fun i hi => by
    obtain ⟨h0, h1⟩ := hαI i hi
    simp only [hK, hT]
    rw [exp_log_add_mul_I (by linarith [(polarRadius_four_mul_bounds h0 h1).1]), tmplPt_of_mem h0 h1]
  have hnear_lo : ∀ i, i < k → ∀ q ∈ H.cell (v i), ‖tmplCoord z r ϑ q - T i‖ < 1 / 60 :=
    fun i hi q hq => hW.coord_near hr (by omega)
      ⟨hW.monotone_α (Nat.le_succ i), hW.overlap i (by omega)⟩ hq
  have hnear_hi : ∀ i, i < k → ∀ q ∈ H.cell (v (i + 1)), ‖tmplCoord z r ϑ q - T i‖ < 1 / 60 :=
    fun i hi q hq => hW.coord_near hr (by omega) ⟨le_rfl, (hW.bounds (i + 1) (by omega)).2.1⟩ hq
  have hPne : ∀ i, i < k → P i / T i ≠ 0 := fun i hi h0 => by
    have := re_div_pos_of_near (hTnorm i hi) (hnear_lo i hi _ (D.Ψ_pt (v i)))
    simp only [hP] at h0
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have hPne' : ∀ i, i < k → P (i + 1) / T i ≠ 0 := fun i hi h0 => by
    have := re_div_pos_of_near (hTnorm i hi) (hnear_hi i hi _ (D.Ψ_pt (v (i + 1))))
    simp only [hP] at h0
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have hℓm_exp : ∀ i, i < k → Complex.exp (ℓm i) = P i := fun i hi => by
    simp only [hℓm]
    rw [Complex.exp_add, Complex.exp_log (hPne i hi), hKexp i hi, div_mul_cancel₀ _ (hT0 i hi)]
  have hℓp_exp : ∀ i, i < k → Complex.exp (ℓp i) = P (i + 1) := fun i hi => by
    simp only [hℓp]
    rw [Complex.exp_add, Complex.exp_log (hPne' i hi), hKexp i hi, div_mul_cancel₀ _ (hT0 i hi)]
  have hKim : ∀ i, (K i).im = Θ i := fun i => by simp [hK]
  have hℓm_im : ∀ i, (ℓm i).im = Complex.arg (P i / T i) + Θ i := fun i => by
    simp only [hℓm, Complex.add_im, Complex.log_im, hKim]
  have hℓp_im : ∀ i, (ℓp i).im = Complex.arg (P (i + 1) / T i) + Θ i := fun i => by
    simp only [hℓp, Complex.add_im, Complex.log_im, hKim]
  -- Claim A: consecutive logarithms agree
  have hA : ∀ i, j ≤ i → i + 2 ≤ k → ℓp i = ℓm (i + 1) := by
    intro i hji hik
    refine eq_of_exp_eq_of_abs_im_sub_lt ((hℓp_exp i (by omega)).trans (hℓm_exp (i + 1) (by omega)).symm) ?_
    rw [hℓp_im, hℓm_im]
    have h1 := abs_arg_div_lt_of_near (hTnorm i (by omega)) (hnear_hi i (by omega) _ (D.Ψ_pt (v (i + 1))))
    have h2 := abs_arg_div_lt_of_near (hTnorm (i + 1) (by omega))
      (hnear_lo (i + 1) (by omega) _ (D.Ψ_pt (v (i + 1))))
    have hmono : α (i + 1) ≤ α (i + 1 + 1) := hW.monotone_α (Nat.le_succ _)
    have hθ1 : Θ i ≤ Θ (i + 1) := polarAngle_mono (by linarith)
    have hθ2 : Θ (i + 1) - Θ i ≤ 7 * (4 * α (i + 1 + 1) - 4 * α (i + 1)) := polarAngle_sub_le (by linarith)
    have hov := hW.overlap (i + 1) (by omega)
    have hb := (hW.bounds (i + 1) (by omega)).2.2.2
    rw [abs_lt] at h1 h2 ⊢
    constructor <;> nlinarith
  -- Claim B: the two ends differ by `2πi`
  have hB : ℓp (k - 1) = ℓm j + 2 * Real.pi * Complex.I := by
    have hPjk : P (k - 1 + 1) = P j := by
      simp only [hP, show k - 1 + 1 = k by omega, hv]
    refine eq_add_two_pi_I_of_exp_eq ((hℓp_exp (k - 1) (by omega)).trans
      (hPjk.trans (hℓm_exp j hjk).symm)) ?_ ?_ <;> rw [hℓp_im, hℓm_im]
    all_goals
      have h1 := abs_arg_div_lt_of_near (hTnorm (k - 1) (by omega))
        (hnear_hi (k - 1) (by omega) _ (D.Ψ_pt (v (k - 1 + 1))))
      have h2 := abs_arg_div_lt_of_near (hTnorm j hjk) (hnear_lo j hjk _ (D.Ψ_pt (v j)))
      have hΘk : 2 * Real.pi - 1 / 10 ≤ Θ (k - 1) ∧ Θ (k - 1) ≤ 2 * Real.pi + 1 / 10 := by
        simp only [hΘ, show k - 1 + 1 = k by omega]
        have := (hW.bounds k hkn)
        exact polarAngle_bounds_on_final (by linarith) (by linarith [this.2.1, this.2.2.1])
      have hΘj : Θ j = 0 := by
        simp only [hΘ]
        have := hW.overlap j (by omega)
        exact polarAngle_eq_zero_on_radial (by linarith)
      rw [abs_lt] at h1 h2
      rw [hΘj]
    · linarith
    · linarith
  -- the dart increments
  have hincr : ∀ t, j ≤ t → t < j + (k - j) → ∀ ht : t < n,
      dartIncr D z ⟨(v t, v (t + 1)), hW.adj t ht⟩ = ℓp t - ℓm t := by
    intro t ht1 ht2 htn
    have hc : (tmplFactor r ϑ * T t)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (tmplFactor_ne_zero hr ϑ) (hT0 t (by omega)))
    have hform : ∀ w : ℂ, (tmplFactor r ϑ * T t)⁻¹ * (w - z) = tmplCoord z r ϑ w / T t := fun w => by
      rw [← div_eq_inv_mul, sub_div_tmplFactor_mul]
    rw [dartIncr_eq_log_sub_log_of_cells D z _ hc]
    · simp only [hform, hℓp, hℓm, hP]
      ring
    · rintro q (hq | hq) <;> rw [hform] <;> refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
      · exact re_div_pos_of_near (hTnorm t (by omega)) (hnear_lo t (by omega) q hq)
      · exact re_div_pos_of_near (hTnorm t (by omega)) (hnear_hi t (by omega) q hq)
  -- the sum telescopes
  set f : ℕ → ℂ := fun t => if t < k - j then ℓm (j + t) else ℓp (j + t - 1) with hf
  have hsum_eq : ∑ t ∈ Finset.range (k - j), (ℓp (j + t) - ℓm (j + t)) =
      ∑ t ∈ Finset.range (k - j), (f (t + 1) - f t) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    have hft : f t = ℓm (j + t) := by simp only [hf, ht, ↓reduceIte]
    rw [hft]
    by_cases ht1 : t + 1 < k - j
    · have : f (t + 1) = ℓm (j + (t + 1)) := by simp only [hf, ht1, ↓reduceIte]
      rw [this, hA (j + t) (by omega) (by omega)]
      rfl
    · have : f (t + 1) = ℓp (j + (t + 1) - 1) := by simp only [hf, ht1, ↓reduceIte]
      rw [this, show j + (t + 1) - 1 = j + t by omega]
  have hsum : walkIncr D z W = 2 * Real.pi * Complex.I := by
    have hcopy : ∀ {a b a' b' : V} (p : G.adj.Walk a b) (ha : a = a') (hb : b = b'),
        dartSum (dartIncr D z) (p.copy ha hb) = dartSum (dartIncr D z) p := by
      intro a b a' b' p ha hb
      subst ha hb
      rfl
    rw [walkIncr, hWdef, hcopy, dartSum_walkAlongSeq v hW.adj (dartIncr D z) (fun t => ℓp t - ℓm t) (k - j) j hlen
      hincr, hsum_eq, Finset.sum_range_sub]
    have hfk : f (k - j) = ℓp (k - 1) := by
      simp only [hf, lt_irrefl, ↓reduceIte, show j + (k - j) - 1 = k - 1 by omega]
    have hf0 : f 0 = ℓm j := by
      simp only [hf, show 0 < k - j by omega, ↓reduceIte, Nat.add_zero]
    rw [hfk, hf0, hB]
    ring
  have hdeg : loopDeg (drawnLoop D W - ContinuousMap.const unitInterval z) hne = 1 := by
    have h := loopDeg_drawnLoop_mul D W hne
    rw [hsum] at h
    have h2 : ((loopDeg (drawnLoop D W - ContinuousMap.const unitInterval z) hne : ℂ) - 1) *
        (2 * Real.pi * Complex.I) = 0 := by
      rw [sub_mul, h, one_mul, sub_self]
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact_mod_cast sub_eq_zero.1 h3
    · exact absurd h3 two_pi_I_ne_zero'
  exact ⟨W, hann, ⟨hne, by rw [hdeg]; exact one_ne_zero⟩, hWsupp⟩

end MatedCRTHarmonic.RouteM
