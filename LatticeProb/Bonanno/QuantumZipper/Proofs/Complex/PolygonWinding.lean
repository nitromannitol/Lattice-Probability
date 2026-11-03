/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.PolygonWinding at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.PolygonWindingBasic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoSep
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Winding numbers of closed polygons: vanishing at infinity and local constancy (EXT-CA node H2, part 2)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 "H. Homology Cauchy", node H2; the definition of
`wind` and its integrality are in `Proofs/Complex/PolygonWindingBasic.lean`.

* `norm_wind_le`, `wind_eq_zero_of_large`: the winding number of a closed polygon vanishes far from
  its carrier (the integrand is `O(1/‖a‖)` by the node-H1 length bound);
* `norm_wind_sub_le`, `wind_locallyConstant`: `wind p` is locally constant off the carrier;
* `continuousOn_windInt`: the integer-valued winding number is continuous (locally constant) on the
  complement of the carrier;
* `wind_eq_zero_of_mem_connectedComponentIn`: `wind p a = 0` on the unbounded component of the
  complement of the carrier (T6 of `Proofs/Complex/TopoSep.lean` plus local constancy).

## Sources

R. B. Burckel, *Classical Analysis in the Complex Plane* (Birkhäuser 2021), Corollary 4.3
(printed p. 189): the index is integer valued, locally constant, and `0` on the unbounded component,
hence constant on each component of the complement of the trace.  (Citation corrected by
AUDIT10 C10-3: the earlier "Theorem 4.6" is an exercise, and Corollary 4.3 is the statement used.)
The constants in the local-constancy lemma are chosen so that two nearby integral values of `wind`
differ by `< 1`.
-/

noncomputable section

open Set Metric Filter Complex Real AffineMap MeasureTheory
open scoped Topology Convex

namespace QuantumZipper.CA.Homology

/-! ## The carrier is bounded and compact -/

theorem walkLength_nonneg (u : ℂ) (l : List ℂ) : 0 ≤ walkLength u l := by
  induction l generalizing u with
  | nil => simp [walkLength]
  | cons v t ih => rw [walkLength_cons]; exact add_nonneg (norm_nonneg _) (ih v)

/-- Points of the walk are within the length of the walk from its starting point. -/
theorem norm_sub_le_walkLength {u : ℂ} :
    ∀ (l : List ℂ) {z : ℂ}, z ∈ walkCarrier u l → ‖z - u‖ ≤ walkLength u l
  | [], z, hz => by simp [walkCarrier] at hz
  | v :: t, z, hz => by
    rw [walkCarrier_cons] at hz
    rw [walkLength_cons]
    rcases hz with hz | hz
    · have h1 := norm_sub_le_of_mem_segment (x := u) (y := z) (z := v) hz
      rw [norm_sub_rev v u] at h1
      exact h1.trans (le_add_of_nonneg_right (walkLength_nonneg v t))
    · calc ‖z - u‖ ≤ ‖z - v‖ + ‖v - u‖ := by
            rw [show z - u = (z - v) + (v - u) from by ring]
            exact norm_add_le (z - v) (v - u)
        _ ≤ walkLength v t + ‖v - u‖ := add_le_add (norm_sub_le_walkLength t hz) le_rfl
        _ = walkLength u (v :: t) := by rw [walkLength_cons, norm_sub_rev v u]; exact add_comm _ _

/-- The carrier of a polygon lies in a ball around the origin. -/
theorem carrier_subset_ball (p : Polygon) :
    p.carrier ⊆ Metric.ball 0 (1 + (‖p.head‖ + walkLength p.head p.rest)) := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right]
  have h1 : ‖z - p.head‖ ≤ walkLength p.head p.rest := norm_sub_le_walkLength p.rest hz
  have h2 : ‖z‖ ≤ ‖z - p.head‖ + ‖p.head‖ := by
    calc ‖z‖ = ‖(z - p.head) + p.head‖ := by
          conv_lhs => rw [show z = (z - p.head) + p.head from by ring]
      _ ≤ ‖z - p.head‖ + ‖p.head‖ := norm_add_le (z - p.head) p.head
  linarith

theorem isCompact_segmentC (u v : ℂ) : IsCompact (segment ℝ u v) := by
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image (continuous_lineMap u v)

theorem isCompact_walkCarrier (u : ℂ) (l : List ℂ) : IsCompact (walkCarrier u l) := by
  induction l generalizing u with
  | nil => simp [walkCarrier]
  | cons v t ih => rw [walkCarrier_cons]; exact (isCompact_segmentC u v).union (ih v)

theorem Polygon.isCompact_carrier (p : Polygon) : IsCompact p.carrier :=
  isCompact_walkCarrier p.head p.rest

/-! ## The winding number is small far from the carrier -/

/-- The integrand `dz/(z-a)` is small on the carrier when `a` is far from it. -/
theorem norm_wind_le (p : Polygon) {R : ℝ} (hR : p.carrier ⊆ Metric.ball 0 R) {a : ℂ}
    (hRa : R < ‖a‖) :
    ‖wind p a‖ ≤ ‖(2 * π * I)⁻¹‖ * (p.length * (1 / (‖a‖ - R))) := by
  rw [wind, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine norm_walkIntegral_le (fun z => (z - a)⁻¹) p.head p.rest ?_
  intro z hz
  have hzR : ‖z‖ < R := by
    have h := hR hz
    rwa [Metric.mem_ball, dist_zero_right] at h
  have h2 : ‖a‖ ≤ ‖z - a‖ + ‖z‖ := by
    have h4 : ‖a‖ ≤ ‖a - z‖ + ‖z‖ := by
      calc ‖a‖ = ‖(a - z) + z‖ := by
            conv_lhs => rw [show a = (a - z) + z from by ring]
        _ ≤ ‖a - z‖ + ‖z‖ := norm_add_le (a - z) z
    rwa [norm_sub_rev a z] at h4
  have h3 : (0 : ℝ) < ‖a‖ - R := by linarith
  rw [norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le h3 (by linarith : ‖a‖ - R ≤ ‖z - a‖)

/-- **Vanishing at infinity.** Far from the carrier the winding number of a closed polygon is `0`. -/
theorem wind_eq_zero_of_large (p : Polygon) (hcl : p.last = p.head) {R : ℝ}
    (hR : p.carrier ⊆ Metric.ball 0 R) {a : ℂ}
    (hbig : R + p.length * ‖(2 * π * I)⁻¹‖ + 1 < ‖a‖) : wind p a = 0 := by
  have hL : (0 : ℝ) ≤ p.length * ‖(2 * π * I)⁻¹‖ :=
    mul_nonneg (by rw [Polygon.length_def]; exact walkLength_nonneg _ _) (norm_nonneg _)
  have ha : a ∉ p.carrier := by
    intro h
    have h1 := hR h
    rw [Metric.mem_ball, dist_zero_right] at h1
    linarith
  obtain ⟨n, hn⟩ := exists_int_wind p hcl a ha
  have hsmall : ‖wind p a‖ < 1 := by
    refine lt_of_le_of_lt (norm_wind_le p hR (by linarith)) ?_
    have hpos : (0 : ℝ) < ‖a‖ - R := by linarith
    have hlt : ‖(2 * π * I)⁻¹‖ * p.length < ‖a‖ - R := by linarith
    calc ‖(2 * π * I)⁻¹‖ * (p.length * (1 / (‖a‖ - R)))
        = ‖(2 * π * I)⁻¹‖ * p.length / (‖a‖ - R) := by ring
      _ < 1 := (div_lt_one hpos).mpr hlt
  rw [hn] at hsmall
  have h2 : |(n : ℝ)| < 1 := by simpa using hsmall
  have h3 : n = 0 := by
    by_contra h0
    have h4 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs h0
      exact_mod_cast this
    linarith
  rw [hn, h3]
  simp

/-! ## Local constancy and the unbounded component -/

/-- **Lipschitz estimate.** If both `a` and `b` keep distance `r > 0` from the carrier, then
`‖wind p b - wind p a‖ ≤ ‖(2πi)⁻¹‖ · length · ‖b-a‖/r²`: the difference of the two integrands
`(z-b)⁻¹ - (z-a)⁻¹ = (b-a)/((z-b)(z-a))` is small. -/
theorem norm_wind_sub_le (p : Polygon) {a b : ℂ} {r : ℝ} (hr : 0 < r)
    (har : ∀ z ∈ p.carrier, r ≤ ‖z - a‖) (hbr : ∀ z ∈ p.carrier, r ≤ ‖z - b‖) :
    ‖wind p b - wind p a‖ ≤ ‖(2 * π * I)⁻¹‖ * (p.length * (‖b - a‖ / r ^ 2)) := by
  have hsub : wind p b - wind p a
      = (2 * π * I)⁻¹ * (walkIntegral (fun z => (z - b)⁻¹) p.head p.rest
          - walkIntegral (fun z => (z - a)⁻¹) p.head p.rest) := by
    rw [wind, wind]
    ring
  rw [hsub, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine norm_walkIntegral_sub_le p.head p.rest (A := p.carrier) (fun _ hz => hz) ?_ ?_ ?_
  · refine ContinuousOn.inv₀ ((continuous_id.sub continuous_const).continuousOn) fun z hz => ?_
    exact sub_ne_zero.mpr fun h => by
      have h1 := hbr z hz
      rw [← h] at h1
      simp at h1
      linarith
  · refine ContinuousOn.inv₀ ((continuous_id.sub continuous_const).continuousOn) fun z hz => ?_
    exact sub_ne_zero.mpr fun h => by
      have h1 := har z hz
      rw [← h] at h1
      simp at h1
      linarith
  · intro z hz
    have hzb : z - b ≠ 0 := sub_ne_zero.mpr fun h => by
      have h1 := hbr z hz
      rw [← h] at h1
      simp at h1
      linarith
    have hza : z - a ≠ 0 := sub_ne_zero.mpr fun h => by
      have h1 := har z hz
      rw [← h] at h1
      simp at h1
      linarith
    have h1 : (z - b)⁻¹ - (z - a)⁻¹ = (b - a) / ((z - b) * (z - a)) := by
      field_simp
      ring
    have h2 : r * r ≤ ‖z - b‖ * ‖z - a‖ :=
      mul_le_mul (hbr z hz) (har z hz) hr.le (norm_nonneg _)
    calc ‖(z - b)⁻¹ - (z - a)⁻¹‖ = ‖b - a‖ / (‖z - b‖ * ‖z - a‖) := by
          rw [h1, norm_div, norm_mul]
      _ ≤ ‖b - a‖ / (r * r) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hr hr) h2
      _ = ‖b - a‖ / r ^ 2 := by rw [pow_two]

/-- **Local constancy.** Off the carrier, the winding number of a closed polygon is constant on a
neighbourhood (and the neighbourhood stays off the carrier); constants are chosen so that two
nearby integral values differ by `< 1` (Burckel, Theorem 4.6, printed p. 190). -/
theorem wind_locallyConstant (p : Polygon) (hcl : p.last = p.head) (a : ℂ) (ha : a ∉ p.carrier) :
    ∃ ε > 0, ∀ b, ‖b - a‖ < ε → b ∉ p.carrier ∧ wind p b = wind p a := by
  by_cases hempty : p.carrier = ∅
  · have hwind : ∀ c : ℂ, wind p c = 0 := by
      intro c
      have hrest : p.rest = [] := by
        by_contra hne
        have hne' : (walkCarrier p.head p.rest).Nonempty := by
          cases h : p.rest with
          | nil => exact absurd h hne
          | cons v t => exact ⟨p.head, Or.inl (left_mem_segment ℝ p.head v)⟩
        rw [← Polygon.carrier_def, hempty] at hne'
        exact hne'.ne_empty rfl
      rw [wind, hrest]
      simp [walkIntegral]
    refine ⟨1, one_pos, fun b _ => ⟨?_, by rw [hwind b, hwind a]⟩⟩
    rw [hempty]
    simp
  · obtain ⟨z₀, hz₀⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    have hcont : ContinuousOn (fun z : ℂ => ‖z - a‖) p.carrier := by fun_prop
    obtain ⟨z₁, hz₁, hmin⟩ := p.isCompact_carrier.exists_isMinOn ⟨z₀, hz₀⟩ hcont
    set r : ℝ := ‖z₁ - a‖ with hr
    have hrpos : 0 < r := by
      rw [hr]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr fun h => ha (h ▸ hz₁))
    have hle : ∀ z ∈ p.carrier, r ≤ ‖z - a‖ := fun z hz => hmin hz
    have hL : (0 : ℝ) ≤ p.length := by
      rw [Polygon.length_def]
      exact walkLength_nonneg _ _
    have hq : (0 : ℝ) ≤ ‖(2 * π * I)⁻¹‖ := norm_nonneg _
    have hA : (0 : ℝ) < 4 * ‖(2 * π * I)⁻¹‖ * (p.length + 1) + 1 := by positivity
    refine ⟨min (r / 2) (r ^ 2 / (2 * (4 * ‖(2 * π * I)⁻¹‖ * (p.length + 1) + 1))),
      lt_min (by linarith) (by positivity), fun b hb => ?_⟩
    have hb1 : ‖b - a‖ < r / 2 :=
      lt_of_lt_of_le hb (min_le_left _ _)
    have hb2 : ‖b - a‖ < r ^ 2 / (2 * (4 * ‖(2 * π * I)⁻¹‖ * (p.length + 1) + 1)) :=
      lt_of_lt_of_le hb (min_le_right _ _)
    have hbC : b ∉ p.carrier := fun hbc => by
      have h1 := hle b hbc
      linarith
    refine ⟨hbC, ?_⟩
    -- both points keep distance `r/2` from the carrier
    have h1 : ∀ z ∈ p.carrier, r / 2 ≤ ‖z - b‖ := by
      intro z hz
      have h2 : r ≤ ‖z - a‖ := hle z hz
      have h3 : ‖a - b‖ < r / 2 := by
        simpa only [norm_sub_rev a b] using hb1
      have h4 : ‖z - a‖ ≤ ‖z - b‖ + ‖b - a‖ := by
        rw [show z - a = (z - b) + (b - a) from by ring]
        exact norm_add_le (z - b) (b - a)
      rw [norm_sub_rev b a] at h4
      linarith
    have hbnd := norm_wind_sub_le (p := p) (a := a) (b := b) (r := r / 2)
      (by linarith : (0 : ℝ) < r / 2) (fun z hz => by linarith [hle z hz]) h1
    have hsmall : ‖wind p b - wind p a‖ < 1 := by
      refine lt_of_le_of_lt hbnd ?_
      rw [show (r / 2) ^ 2 = r ^ 2 / 4 from by ring]
      have h2A : (0 : ℝ) < 2 * (4 * ‖(2 * π * I)⁻¹‖ * (p.length + 1) + 1) := by positivity
      have hb2' : ‖b - a‖ * (2 * (4 * ‖(2 * π * I)⁻¹‖ * (p.length + 1) + 1)) < r ^ 2 :=
        (lt_div_iff₀ h2A).mp hb2
      have h4q : 4 * ‖(2 * π * I)⁻¹‖ * p.length
          ≤ 4 * ‖(2 * π * I)⁻¹‖ * (p.length + 1) := by
        have h5 : p.length ≤ p.length + 1 := by linarith
        exact mul_le_mul_of_nonneg_left h5 (by positivity)
      have hr2 : (0 : ℝ) < r ^ 2 := by positivity
      have hkey : 4 * ‖(2 * π * I)⁻¹‖ * p.length * ‖b - a‖ < r ^ 2 := by
        have h6 : 4 * ‖(2 * π * I)⁻¹‖ * p.length * ‖b - a‖
            ≤ 4 * ‖(2 * π * I)⁻¹‖ * (p.length + 1) * ‖b - a‖ :=
          mul_le_mul_of_nonneg_right h4q (norm_nonneg _)
        have h7 : 4 * ‖(2 * π * I)⁻¹‖ * (p.length + 1) * ‖b - a‖
            ≤ (2 * (4 * ‖(2 * π * I)⁻¹‖ * (p.length + 1) + 1)) * ‖b - a‖ := by
          have h8 : (0 : ℝ) ≤ 4 * ‖(2 * π * I)⁻¹‖ * (p.length + 1) := by positivity
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          linarith
        have h9 : (2 * (4 * ‖(2 * π * I)⁻¹‖ * (p.length + 1) + 1)) * ‖b - a‖
            = ‖b - a‖ * (2 * (4 * ‖(2 * π * I)⁻¹‖ * (p.length + 1) + 1)) := by ring
        linarith
      calc ‖(2 * π * I)⁻¹‖ * (p.length * (‖b - a‖ / (r ^ 2 / 4)))
          = 4 * ‖(2 * π * I)⁻¹‖ * p.length * ‖b - a‖ / r ^ 2 := by ring
        _ < 1 := (div_lt_one hr2).mpr hkey
    obtain ⟨nb, hnb⟩ := exists_int_wind p hcl b hbC
    obtain ⟨na, hna⟩ := exists_int_wind p hcl a ha
    have hEq : nb = na := by
      have h2 : ‖(nb : ℂ) - (na : ℂ)‖ < 1 := by
        rw [← hnb, ← hna]
        exact hsmall
      have h3 : |(nb : ℝ) - (na : ℝ)| < 1 := by
        have h4 := Complex.abs_re_le_norm ((nb : ℂ) - (na : ℂ))
        have h5 : (((nb : ℂ) - (na : ℂ))).re = (nb : ℝ) - (na : ℝ) := by simp
        rw [h5] at h4
        linarith
      have h4 : nb - na = 0 := by
        by_contra h0
        have h5 : (1 : ℝ) ≤ |(nb : ℝ) - (na : ℝ)| := by
          have h6 : ((nb - na : ℤ) : ℝ) = (nb : ℝ) - (na : ℝ) := by push_cast; ring
          have h7 : (1 : ℤ) ≤ |nb - na| := Int.one_le_abs h0
          have h8 : ((1 : ℤ) : ℝ) ≤ ((|nb - na| : ℤ) : ℝ) := by exact_mod_cast h7
          rw [Int.cast_abs, h6, Int.cast_one] at h8
          exact h8
        linarith
      omega
    rw [hnb, hna, hEq]

/-- The winding number of a polygon at a point off its carrier, as an integer (an arbitrary value
off the carrier, where the winding number need not be an integer). -/
noncomputable def windInt (p : Polygon) (a : ℂ) : ℤ := by
  classical
  exact if h : ∃ n : ℤ, wind p a = (n : ℂ) then h.choose else 0

theorem windInt_spec (p : Polygon) (hcl : p.last = p.head) {a : ℂ} (ha : a ∉ p.carrier) :
    (windInt p a : ℂ) = wind p a := by
  classical
  obtain ⟨n, hn⟩ := exists_int_wind p hcl a ha
  have hex : ∃ m : ℤ, wind p a = (m : ℂ) := ⟨n, hn⟩
  have h1 : windInt p a = hex.choose := by
    unfold windInt
    rw [dite_eq_left hex]
  rw [h1]
  exact (Classical.choose_spec hex).symm

/-- **Local constancy, integer form.** On any subset of the complement of the carrier, the
integer-valued winding number is continuous (locally constant). -/
theorem continuousOn_windInt (p : Polygon) (hcl : p.last = p.head) {S : Set ℂ}
    (hS : S ⊆ p.carrierᶜ) : ContinuousOn (windInt p) S := by
  intro x hx
  obtain ⟨ε, hε, hloc⟩ := wind_locallyConstant p hcl x (hS hx)
  rw [Metric.continuousWithinAt_iff]
  intro δ hδ
  refine ⟨ε, hε, fun y hy hxy => ?_⟩
  have hxy' : ‖y - x‖ < ε := by rwa [dist_eq_norm] at hxy
  have hyC : y ∉ p.carrier := (hloc y hxy').1
  have h1 : (windInt p y : ℂ) = (windInt p x : ℂ) := by
    rw [windInt_spec p hcl hyC, windInt_spec p hcl (hS hx)]
    exact (hloc y hxy').2
  have h2 : windInt p y = windInt p x := Int.cast_injective h1
  rw [h2, dist_self]
  exact hδ

/-- **H2, the unbounded component.** On the unbounded component of the complement of the carrier,
the winding number of a closed polygon vanishes (T6 of `Proofs/Complex/TopoSep.lean` plus local
constancy). -/
theorem wind_eq_zero_of_mem_connectedComponentIn (p : Polygon) (hcl : p.last = p.head) {R : ℝ}
    (hR : p.carrier ⊆ Metric.ball 0 R) {a a₀ : ℂ}
    (ha₀ : R + p.length * ‖(2 * π * I)⁻¹‖ + 1 < ‖a₀‖)
    (ha : a ∈ connectedComponentIn p.carrierᶜ a₀) : wind p a = 0 := by
  have hL : (0 : ℝ) ≤ p.length * ‖(2 * π * I)⁻¹‖ :=
    mul_nonneg (by rw [Polygon.length_def]; exact walkLength_nonneg _ _) (norm_nonneg _)
  have ha₀C : a₀ ∉ p.carrier := by
    intro h
    have h1 := hR h
    rw [Metric.mem_ball, dist_zero_right] at h1
    linarith
  have ha₀cc : a₀ ∈ connectedComponentIn p.carrierᶜ a₀ := mem_connectedComponentIn ha₀C
  have hsub := connectedComponentIn_subset p.carrierᶜ a₀
  have hpre : IsPreconnected (connectedComponentIn p.carrierᶜ a₀) :=
    isPreconnected_connectedComponentIn
  have heq : windInt p a = windInt p a₀ :=
    hpre.constant (continuousOn_windInt p hcl hsub) ha ha₀cc
  have h0 : wind p a₀ = 0 := wind_eq_zero_of_large p hcl hR ha₀
  have h1 : (windInt p a : ℂ) = 0 := by
    rw [heq, windInt_spec p hcl (hsub ha₀cc), h0]
  rw [← windInt_spec p hcl (hsub ha)]
  exact h1

end QuantumZipper.CA.Homology
