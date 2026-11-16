import LatticeProb.Analysis.Elliptic.Domain
import LatticeProb.Analysis.Elliptic.HolderCompositionConvex

/-!
# Hölder bounds for first derivatives on `C^{2,σ}` domains

On a bounded domain `U = {ρ < 0}` whose `C¹` defining function has nonzero derivative on its zero
set, nearby points are joined inside `U` by three segments: along a fixed vector, across, and back.
The total length is at most a fixed multiple of the distance of the endpoints. The mean value
inequality along these segments bounds increments of first partial derivatives by the second
derivatives at small distances, and the supremum norm bounds them at large distances. Together
these give a bound for the Hölder seminorm of each first partial derivative by the coordinate
`C^{2,σ}` norm, with a constant depending only on the domain.
-/

open scoped Topology ContDiff

namespace LatticeProb.Elliptic.HolderExtension

open LatticeProb.Euclidean.Lattice

/-- Along a segment inside an open set where `u` is `C²`, the coordinate `C^{2,σ}` norm bounds the
increment of a first partial derivative. -/
private theorem abs_sub_partialDeriv_le_of_segment {d : ℕ} {σ : ℝ} {U : Set (Fin d → ℝ)}
    {u : (Fin d → ℝ) → ℝ} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hn : c2HolderNorm σ U u < ⊤) (i : Fin d) {x y : Fin d → ℝ} (hxy : segment ℝ x y ⊆ U) :
    |partialDeriv i u x - partialDeriv i u y| ≤
      (d * (c2HolderNorm σ U u).toReal) * ‖x - y‖ := by
  have hd (z : Fin d → ℝ) (hz : z ∈ U) : DifferentiableAt ℝ (fderiv ℝ u) z :=
    ((hu.fderiv_of_isOpen (m := 1) hU (by norm_num)).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hp (z : Fin d → ℝ) (hz : z ∈ segment ℝ x y) :
      DifferentiableAt ℝ (partialDeriv i u) z :=
    (hd z (hxy hz)).clm_apply (differentiableAt_const _)
  have hbound (z : Fin d → ℝ) (hz : z ∈ segment ℝ x y) :
      ‖fderiv ℝ (partialDeriv i u) z‖ ≤ d * (c2HolderNorm σ U u).toReal := by
    apply norm_linearMap_le_of_coordinate_bound _ ENNReal.toReal_nonneg
    intro j
    have heq : fderiv ℝ (partialDeriv i u) z (Pi.single j 1) = secondPartial j i u z := by
      change fderiv ℝ (fun w => fderiv ℝ u w (Pi.single i 1)) z (Pi.single j 1) = _
      rw [fderiv_clm_apply (hd z (hxy hz)) (differentiableAt_const _)]
      simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
        ContinuousLinearMap.flip_apply, secondPartial, iteratedFDeriv_two_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [heq]
    exact abs_secondPartial_le_c2HolderNorm_toReal hn j i (hxy hz)
  simpa only [Real.norm_eq_abs] using
    (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le hp hbound
      (right_mem_segment ℝ x y) (left_mem_segment ℝ x y)

/-- In a bounded domain `{ρ < 0}` whose `C¹` defining function has nonzero derivative on its zero
set, any two points at distance less than `δ` are joined inside the domain by three segments: from
`x` to `x + h • v`, from there to `y + h • v`, and back to `y`, where `‖v‖ ≤ 1` and
`h ≤ L * ‖x - y‖`. -/
theorem exists_three_segments {d : ℕ} {U : Set (Fin d → ℝ)} {ρ : (Fin d → ℝ) → ℝ}
    (hUb : Bornology.IsBounded U) (hρ : ContDiff ℝ 1 ρ) (hUρ : U = {x | ρ x < 0})
    (hreg : ∀ x, ρ x = 0 → fderiv ℝ ρ x ≠ 0) :
    ∃ δ > 0, ∃ L ≥ 0, ∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ < δ →
      ∃ v : Fin d → ℝ, ∃ h : ℝ, 0 ≤ h ∧ ‖v‖ ≤ 1 ∧ h ≤ L * ‖x - y‖ ∧
        segment ℝ x (x + h • v) ⊆ U ∧ segment ℝ (x + h • v) (y + h • v) ⊆ U ∧
          segment ℝ (y + h • v) y ⊆ U := by
  have hρd : Differentiable ℝ ρ := hρ.differentiable one_ne_zero
  have hρc : Continuous ρ := hρd.continuous
  have hDρ : Continuous (fderiv ℝ ρ) := hρ.continuous_fderiv one_ne_zero
  have hmemU : ∀ z, z ∈ U ↔ ρ z < 0 := fun z => by rw [hUρ]; rfl
  obtain ⟨R, hR⟩ := hUb.subset_closedBall (0 : Fin d → ℝ)
  obtain ⟨G₀, hG₀⟩ :=
    (isCompact_closedBall (0 : Fin d → ℝ) R).exists_bound_of_continuousOn hDρ.continuousOn
  set G := max G₀ 0 with hGdef
  have hG0 : 0 ≤ G := le_max_right _ _
  have hG : ∀ x ∈ U, ‖fderiv ℝ ρ x‖ ≤ G := fun x hx => (hG₀ x (hR hx)).trans (le_max_left _ _)
  have hcl : closure U ⊆ {x | ρ x ≤ 0} :=
    closure_minimal (fun x hx => ((hmemU x).mp hx).le) (isClosed_le hρc continuous_const)
  obtain ⟨κ, hκ, hκU⟩ : ∃ κ > 0, ∀ x ∈ U, κ ≤ -ρ x ∨ κ ≤ ‖fderiv ℝ ρ x‖ := by
    rcases (closure U).eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      have := subset_closure hx
      rw [he] at this
      exact absurd this (Set.notMem_empty x)
    · have hF : Continuous fun x => max (-ρ x) ‖fderiv ℝ ρ x‖ := hρc.neg.max hDρ.norm
      obtain ⟨x₀, hx₀, hmin⟩ := hUb.isCompact_closure.exists_isMinOn hne hF.continuousOn
      refine ⟨max (-ρ x₀) ‖fderiv ℝ ρ x₀‖, ?_, fun x hx => ?_⟩
      · rcases (show ρ x₀ ≤ 0 from hcl hx₀).lt_or_eq with hlt | heq
        · exact lt_max_of_lt_left (by linarith)
        · exact lt_max_of_lt_right (norm_pos_iff.mpr (hreg x₀ heq))
      · exact le_max_iff.mp (isMinOn_iff.mp hmin x (subset_closure hx))
  obtain ⟨r, hr, hrU⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_closedBall (0 : Fin d → ℝ) (R + 1)).uniformContinuousOn_of_continuous
      hDρ.continuousOn) (κ / 4) (by positivity)
  set r' := min r 1 with hr'def
  have hr' : 0 < r' := lt_min hr one_pos
  have hkey : ∀ x ∈ U, ∀ p ∈ Metric.ball x r', ∀ q ∈ Metric.ball x r',
      ρ q ≤ ρ p + fderiv ℝ ρ x (q - p) + κ / 4 * ‖q - p‖ := by
    intro x hx p hp q hq
    have hK : ∀ w ∈ Metric.ball x r', w ∈ Metric.closedBall (0 : Fin d → ℝ) (R + 1) := by
      intro w hw
      have h1 : ‖x‖ ≤ R := by simpa using hR hx
      have h2 : ‖w - x‖ < r' := by rwa [Metric.mem_ball, dist_eq_norm] at hw
      have h3 : r' ≤ 1 := min_le_right _ _
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖w‖ = ‖x + (w - x)‖ := by rw [add_sub_cancel]
        _ ≤ ‖x‖ + ‖w - x‖ := norm_add_le _ _
        _ ≤ R + 1 := by linarith
    have hbd : ∀ w ∈ Metric.ball x r', ‖fderiv ℝ ρ w - fderiv ℝ ρ x‖ ≤ κ / 4 := by
      intro w hw
      rw [← dist_eq_norm]
      refine (hrU w (hK w hw) x (hK x (Metric.mem_ball_self hr')) ?_).le
      exact lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _)
    have h := (convex_ball x r').norm_image_sub_le_of_norm_fderiv_le'
      (fun w _ => hρd w) hbd hp hq
    rw [Real.norm_eq_abs] at h
    linarith [le_abs_self (ρ q - ρ p - fderiv ℝ ρ x (q - p))]
  have hside : ∀ x ∈ U, ∀ v : Fin d → ℝ, ∀ h : ℝ, 0 ≤ h → ‖v‖ ≤ 1 →
      fderiv ℝ ρ x v + κ / 4 * ‖v‖ ≤ 0 → ∀ q ∈ U, ‖q - x‖ + h < r' →
        segment ℝ q (q + h • v) ⊆ U := by
    intro x hx v h hh hv hslope q hq hqx z hz
    rw [segment_eq_image', add_sub_cancel_left] at hz
    obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hz
    have hnorm : ‖θ • h • v‖ = θ * h * ‖v‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hθ0, Real.norm_of_nonneg hh, mul_assoc]
    have hθhv : θ * h * ‖v‖ ≤ h :=
      (mul_le_of_le_one_right (mul_nonneg hθ0 hh) hv).trans (mul_le_of_le_one_left hh hθ1)
    have hqb : q ∈ Metric.ball x r' := by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith
    have hzb : q + θ • h • v ∈ Metric.ball x r' := by
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖q + θ • h • v - x‖ = ‖(q - x) + θ • h • v‖ := by congr 1; abel
        _ ≤ ‖q - x‖ + ‖θ • h • v‖ := norm_add_le _ _
        _ < r' := by rw [hnorm]; linarith
    have hk := hkey x hx q hqb _ hzb
    rw [add_sub_cancel_left, hnorm, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hk
    have hprod := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hθ0 hh) hslope
    rw [hmemU] at hq ⊢
    nlinarith
  have hmid : ∀ x ∈ U, ∀ y : Fin d → ℝ, ∀ v : Fin d → ℝ, ∀ h : ℝ, 0 ≤ h → ‖v‖ ≤ 1 →
      ‖y - x‖ + h < r' →
      ρ x + h * (fderiv ℝ ρ x v + κ / 4 * ‖v‖) + (G + κ / 4) * ‖y - x‖ < 0 →
        segment ℝ (x + h • v) (y + h • v) ⊆ U := by
    intro x hx y v h hh hv hyx hneg z hz
    have hdiff : y + h • v - (x + h • v) = y - x := by abel
    rw [segment_eq_image', hdiff] at hz
    obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hz
    have hw : x + h • v + θ • (y - x) - x = h • v + θ • (y - x) := by abel
    have hnorm : ‖h • v + θ • (y - x)‖ ≤ h * ‖v‖ + θ * ‖y - x‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hh, Real.norm_of_nonneg hθ0]
    have hθs : θ * ‖y - x‖ ≤ ‖y - x‖ := mul_le_of_le_one_left (norm_nonneg _) hθ1
    have hhv : h * ‖v‖ ≤ h := mul_le_of_le_one_right hh hv
    have hzb : x + h • v + θ • (y - x) ∈ Metric.ball x r' := by
      rw [Metric.mem_ball, dist_eq_norm, hw]
      linarith
    have hk := hkey x hx x (Metric.mem_ball_self hr') _ hzb
    rw [hw, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hk
    have hDy : fderiv ℝ ρ x (y - x) ≤ G * ‖y - x‖ := by
      have := (fderiv ℝ ρ x).le_opNorm (y - x)
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans
        (this.trans (mul_le_mul_of_nonneg_right (hG x hx) (norm_nonneg _)))
    have h1 : θ * fderiv ℝ ρ x (y - x) ≤ G * ‖y - x‖ :=
      (mul_le_mul_of_nonneg_left hDy hθ0).trans
        (mul_le_of_le_one_left (mul_nonneg hG0 (norm_nonneg _)) hθ1)
    have h2 := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ κ / 4 by positivity)
    rw [hmemU]
    nlinarith
  set L := 4 * G / κ + 1 with hLdef
  have hL0 : 0 ≤ L := by positivity
  refine ⟨min (r' / (L + 1)) (κ / (G + κ)), lt_min (by positivity) (by positivity), L, hL0, ?_⟩
  intro x hx y hy hs
  have hs1 : ‖y - x‖ < r' / (L + 1) := by
    rw [norm_sub_rev]; exact hs.trans_le (min_le_left _ _)
  have hs2 : ‖y - x‖ < κ / (G + κ) := by
    rw [norm_sub_rev]; exact hs.trans_le (min_le_right _ _)
  rw [norm_sub_rev x y]
  set s := ‖y - x‖ with hsdef
  have hs0 : 0 ≤ s := norm_nonneg _
  have hsL : s + L * s < r' := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < L + 1)).mp hs1
    linarith
  have hρx : ρ x < 0 := (hmemU x).mp hx
  obtain ⟨v, h, hh, hv, hhL, hslope, hneg⟩ : ∃ v : Fin d → ℝ, ∃ h : ℝ, 0 ≤ h ∧ ‖v‖ ≤ 1 ∧
      h ≤ L * s ∧ fderiv ℝ ρ x v + κ / 4 * ‖v‖ ≤ 0 ∧
      ρ x + h * (fderiv ℝ ρ x v + κ / 4 * ‖v‖) + (G + κ / 4) * s < 0 := by
    rcases hκU x hx with hdeep | hsteep
    · refine ⟨0, 0, le_rfl, by simp, by positivity, by simp, ?_⟩
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < G + κ)).mp hs2
      nlinarith
    · obtain ⟨w, hw1, hw2⟩ := (fderiv ℝ ρ x).exists_lt_apply_of_lt_opNorm
        (show κ / 2 < ‖fderiv ℝ ρ x‖ by linarith)
      obtain ⟨v, hv1, hv2⟩ : ∃ v : Fin d → ℝ, ‖v‖ ≤ 1 ∧ fderiv ℝ ρ x v ≤ -(κ / 2) := by
        rw [Real.norm_eq_abs] at hw2
        rcases le_or_gt (fderiv ℝ ρ x w) 0 with hnp | hpos
        · rw [abs_of_nonpos hnp] at hw2
          exact ⟨w, hw1.le, by linarith⟩
        · rw [abs_of_pos hpos] at hw2
          exact ⟨-w, by rw [norm_neg]; exact hw1.le, by rw [map_neg]; linarith⟩
      have hslope' : fderiv ℝ ρ x v + κ / 4 * ‖v‖ ≤ -(κ / 4) := by nlinarith [norm_nonneg v]
      have hκL : L * s * (-(κ / 4)) = -((G + κ / 4) * s) := by
        rw [hLdef]; field_simp
      have hprod := mul_le_mul_of_nonneg_left hslope' (show 0 ≤ L * s by positivity)
      refine ⟨v, L * s, by positivity, hv1, le_rfl, by linarith, ?_⟩
      linarith
  refine ⟨v, h, hh, hv, hhL, hside x hx v h hh hv hslope x hx (by simp; linarith),
    hmid x hx y v h hh hv (by linarith) hneg, ?_⟩
  rw [segment_symm]
  exact hside x hx v h hh hv hslope y hy (by linarith)

/-- On a bounded domain with a `C^{2,σ}` defining function, the Hölder seminorm of each first
partial derivative is bounded by a constant multiple of the coordinate `C^{2,σ}` norm. -/
theorem firstDeriv_holder_bound {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (hσ' : σ < 1)
    {U : Set (Fin d → ℝ)} (hU : IsC2HolderDomain σ U) :
    ∃ A : ℝ, 0 < A ∧ ∀ u : (Fin d → ℝ) → ℝ,
      ContDiffOn ℝ 2 u U → c2HolderNorm σ U u < ⊤ →
      ∀ i, holderSeminorm σ U (partialDeriv i u) ≤
        ENNReal.ofReal A * c2HolderNorm σ U u := by
  obtain ⟨hUo, -, hUb, ρ, hρ, -, hUρ, hreg⟩ := hU
  obtain ⟨δ, hδ, L, hL, hseg⟩ :=
    exists_three_segments hUb (hρ.of_le (by norm_num)) hUρ hreg
  have hδσ : 0 < δ ^ σ := Real.rpow_pos_of_pos hδ σ
  refine ⟨d * (2 * L + 1) * δ ^ (1 - σ) + 2 / δ ^ σ, by positivity, ?_⟩
  intro u hu hn i
  set N := (c2HolderNorm σ U u).toReal with hNdef
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  calc holderSeminorm σ U (partialDeriv i u)
      ≤ ENNReal.ofReal ((d * (2 * L + 1) * δ ^ (1 - σ) + 2 / δ ^ σ) * N) := ?_
    _ = ENNReal.ofReal (d * (2 * L + 1) * δ ^ (1 - σ) + 2 / δ ^ σ) * c2HolderNorm σ U u := by
      rw [ENNReal.ofReal_mul (by positivity), hNdef, ENNReal.ofReal_toReal hn.ne]
  refine holderSeminorm_le_of_increment_bound fun x hx y hy => ?_
  set g := partialDeriv i u
  set ρxy := radius (x - y) with hρxy
  have hr0 : 0 ≤ ρxy := radius_nonneg _
  have hsr : ‖x - y‖ ≤ ρxy := pi_norm_le_radius _
  have hrσ : 0 ≤ ρxy ^ σ := Real.rpow_nonneg hr0 σ
  have hdN : 0 ≤ (d : ℝ) * N := mul_nonneg (Nat.cast_nonneg _) hN
  have hsmall : (d : ℝ) * (2 * L + 1) * δ ^ (1 - σ) * N * ρxy ^ σ ≥ 0 := by positivity
  have hlarge : 2 / δ ^ σ * N * ρxy ^ σ ≥ 0 := by positivity
  rcases lt_or_ge ρxy δ with hlt | hge
  · obtain ⟨v, h, hh, hv, hhL, h1, h2, h3⟩ := hseg x hx y hy (hsr.trans_lt hlt)
    have e1 := abs_sub_partialDeriv_le_of_segment hUo hu hn i h1
    have e2 := abs_sub_partialDeriv_le_of_segment hUo hu hn i h2
    have e3 := abs_sub_partialDeriv_le_of_segment hUo hu hn i h3
    have n1 : ‖x - (x + h • v)‖ ≤ h := by
      rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hh]
      exact mul_le_of_le_one_right hh hv
    have n2 : x + h • v - (y + h • v) = x - y := by abel
    have n3 : ‖y + h • v - y‖ ≤ h := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hh]
      exact mul_le_of_le_one_right hh hv
    rw [n2] at e2
    have htri : |g x - g y| ≤ |g x - g (x + h • v)| + |g (x + h • v) - g (y + h • v)| +
        |g (y + h • v) - g y| := by
      have := abs_add_three (g x - g (x + h • v)) (g (x + h • v) - g (y + h • v))
        (g (y + h • v) - g y)
      ring_nf at this ⊢
      linarith
    have hlip : |g x - g y| ≤ d * N * ((2 * L + 1) * ρxy) := by
      have m1 := mul_le_mul_of_nonneg_left n1 hdN
      have m3 := mul_le_mul_of_nonneg_left n3 hdN
      have m2 := mul_le_mul_of_nonneg_left (hhL.trans
        (mul_le_mul_of_nonneg_left hsr hL)) (show (0 : ℝ) ≤ 2 * (d * N) by positivity)
      have m4 := mul_le_mul_of_nonneg_left hsr hdN
      nlinarith
    have hpow : ρxy ≤ δ ^ (1 - σ) * ρxy ^ σ := by
      have hsplit : ρxy = ρxy ^ σ * ρxy ^ (1 - σ) := by
        rw [← Real.rpow_add' hr0 (by norm_num), add_sub_cancel, Real.rpow_one]
      have hle : ρxy ^ (1 - σ) ≤ δ ^ (1 - σ) :=
        Real.rpow_le_rpow hr0 hlt.le (by linarith)
      calc ρxy = ρxy ^ σ * ρxy ^ (1 - σ) := hsplit
        _ ≤ ρxy ^ σ * δ ^ (1 - σ) := mul_le_mul_of_nonneg_left hle hrσ
        _ = δ ^ (1 - σ) * ρxy ^ σ := mul_comm _ _
    have := mul_le_mul_of_nonneg_left hpow
      (show (0 : ℝ) ≤ d * N * (2 * L + 1) by positivity)
    nlinarith
  · have hbd : |g x - g y| ≤ 2 * N := by
      calc |g x - g y| ≤ |g x| + |g y| := abs_sub _ _
        _ ≤ N + N := add_le_add (abs_partialDeriv_le_c2HolderNorm_toReal hn i hx)
          (abs_partialDeriv_le_c2HolderNorm_toReal hn i hy)
        _ = 2 * N := by ring
    have hpow : δ ^ σ ≤ ρxy ^ σ := Real.rpow_le_rpow hδ.le hge hσ.le
    have hfrac : 2 * N ≤ 2 / δ ^ σ * N * ρxy ^ σ := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hδσ]
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    nlinarith
