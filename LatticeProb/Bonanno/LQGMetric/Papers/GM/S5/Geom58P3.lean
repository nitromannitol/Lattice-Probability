/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58P3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58P2

/-!
# GM Lemma 5.8: the end paths `L̂_x`, `L̂_y` are `R` apart (task P2-M2L58c)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Step 2 (l. 3080–3086; GM: the paths are at distance `≥ ρr` from each other). Own
elementary verification for the explicit paths of `Geom58P2`: inner pieces are separated by real
parts, radials from the inner pieces by `dist_rad_vert`, polar pieces by radius or by angle
(`dist_polPt_angle_sep`, minimal angular gap `κ = 10R / (1.1 r)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Real

namespace LQGMetric.GM

/-- the minimal angular gap -/
def kap (r R : ℝ) : ℝ := 10 * R / (11 / 10 * r)

lemma kap_pos {r R : ℝ} (hr : 0 < r) (hR : 0 < R) : 0 < kap r R := by unfold kap; positivity

lemma kap_le {r R : ℝ} (hr : 0 < r) (hRr : 500 * R ≤ r) : kap r R ≤ π / 2 := by
  unfold kap
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Real.two_le_pi]

lemma kap_dist {r R : ℝ} (hr : 0 < r) (hR : 0 < R) : R ≤ 11 / 10 * r * (2 / π * kap r R) := by
  unfold kap
  have hpi := Real.pi_pos
  have e : 11 / 10 * r * (2 / π * (10 * R / (11 / 10 * r))) = 20 * R / π := by
    field_simp; ring
  rw [e, le_div_iff₀ hpi]
  nlinarith [Real.pi_le_four]

/-- angular separation at the scale `R` -/
lemma angle_sepR {r R s s' α β : ℝ} (hr : 0 < r) (hR : 0 < R) (hRr : 500 * R ≤ r)
    (hs : 11 / 10 * r ≤ s) (hs' : 11 / 10 * r ≤ s') (h1 : kap r R ≤ β - α)
    (h2 : β - α ≤ 2 * π - kap r R) : R ≤ dist (polPt s α) (polPt s' β) :=
  (kap_dist hr hR).trans (dist_polPt_angle_sep (by positivity) hs hs' (kap_pos hr hR).le
    (kap_le hr hRr) h1 h2)

lemma norm_sepR {p q : ℂ} {a b R : ℝ} (hp : ‖p‖ ≤ a) (hq : b ≤ ‖q‖) (hab : a + R ≤ b) :
    R ≤ dist p q := by
  have := norm_sub_le_dist p q
  linarith [neg_abs_le (‖p‖ - ‖q‖)]

lemma foot_cos {r t : ℝ} (hr : 0 < r) (ht : |t| ≤ r / 2) :
    11 / 10 * r * Real.cos (arccos (t / (11 / 10 * r))) = t := by
  have hρ : (0 : ℝ) < 11 / 10 * r := by positivity
  rw [Real.cos_arccos (by rw [le_div_iff₀ hρ]; linarith [(abs_le.1 ht).1])
    (by rw [div_le_iff₀ hρ]; linarith [(abs_le.1 ht).2])]
  field_simp

/-- a radial from the circle `1.1 r` with foot at real part `t` vs an inner point -/
lemma rad_inner_sep {r R t s γ : ℝ} {q : ℂ} (hr : 0 < r) (hcos : 11 / 10 * r * Real.cos γ = t)
    (hs : 11 / 10 * r ≤ s) (hq : ‖q‖ ≤ 11 / 10 * r) (hgap : 2 * R ≤ |t - q.re|) :
    R ≤ dist (polPt s γ) q := by
  have := dist_rad_vert (a := q.re) (by positivity) hcos hs rfl hq
  linarith

/-! ## The pieces -/

lemma legL_cases {r R T θx : ℝ} {p : ℂ} (hr : 0 < r) (hR : 0 ≤ R) (hRr : 500 * R ≤ r)
    (hT : |T| ≤ r / 2) (hT5 : |T - 5 * R| ≤ r / 2) (hp : p ∈ legL r R T θx) :
    (((p.im = Real.sqrt (r ^ 2 - T ^ 2) ∧ T - 5 * R ≤ p.re ∧ p.re ≤ T - 2 * R) ∨
        p.re = T - 5 * R) ∧ r / 2 ≤ ‖p‖ ∧ ‖p‖ ≤ 11 / 10 * r) ∨
      (∃ s ∈ Icc (11 / 10 * r) (5 / 4 * r), p = polPt s (gA r R T)) ∨
      (∃ φ ∈ Icc (gA r R T) θx, p = polPt (5 / 4 * r) φ) ∨
      (∃ s ∈ Icc (5 / 4 * r) (2 * r), p = polPt s θx) := by
  rcases hp with (((h | h) | ⟨s, hs, rfl⟩) | ⟨φ, hφ, rfl⟩) | ⟨s, hs, rfl⟩
  · obtain ⟨h1, h2, h3⟩ := mem_hSeg.1 h
    refine Or.inl ⟨Or.inl ⟨h1, h2, h3⟩, norm_stub hr hR hRr hT ?_ ?_ h1⟩
    · exact abs_le.2 ⟨by linarith [(abs_le.1 hT5).1], by linarith [(abs_le.1 hT).2]⟩
    · exact abs_le.2 ⟨by linarith, by linarith⟩
  · obtain ⟨h1, h2⟩ := mem_vSeg.1 h
    refine Or.inl ⟨Or.inr h1, norm_vert hr hR hRr hT hT5 ?_ h1 h2⟩
    rw [abs_le]; constructor <;> linarith
  · exact Or.inr (Or.inl ⟨s, hs, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨φ, hφ, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨s, hs, rfl⟩))

lemma legR_cases {r R T' θy : ℝ} {p : ℂ} (hr : 0 < r) (hR : 0 ≤ R) (hRr : 500 * R ≤ r)
    (hT : |T'| ≤ r / 2) (hT5 : |T' + 5 * R| ≤ r / 2) (hp : p ∈ legR r R T' θy) :
    (((p.im = Real.sqrt (r ^ 2 - T' ^ 2) ∧ T' + 2 * R ≤ p.re ∧ p.re ≤ T' + 5 * R) ∨
        p.re = T' + 5 * R) ∧ r / 2 ≤ ‖p‖ ∧ ‖p‖ ≤ 11 / 10 * r) ∨
      (∃ s ∈ Icc (11 / 10 * r) (7 / 4 * r), p = polPt s (gB r R T')) ∨
      (∃ s ∈ Icc (7 / 4 * r) (2 * r), ∃ φ ∈ Icc (min (gB r R T') θy) (max (gB r R T') θy),
        p = polPt s φ) := by
  rcases hp with (((h | h) | ⟨s, hs, rfl⟩) | ⟨φ, hφ, rfl⟩) | ⟨s, hs, rfl⟩
  · obtain ⟨h1, h2, h3⟩ := mem_hSeg.1 h
    refine Or.inl ⟨Or.inl ⟨h1, h2, h3⟩, norm_stub hr hR hRr hT ?_ ?_ h1⟩
    · exact abs_le.2 ⟨by linarith [(abs_le.1 hT).1], by linarith [(abs_le.1 hT5).2]⟩
    · exact abs_le.2 ⟨by linarith, by linarith⟩
  · obtain ⟨h1, h2⟩ := mem_vSeg.1 h
    refine Or.inl ⟨Or.inr h1, norm_vert hr hR hRr hT hT5 ?_ h1 h2⟩
    rw [abs_le]; constructor <;> linarith
  · exact Or.inr (Or.inl ⟨s, hs, rfl⟩)
  · exact Or.inr (Or.inr ⟨7 / 4 * r, ⟨le_rfl, by linarith⟩, φ, hφ, rfl⟩)
  · exact Or.inr (Or.inr ⟨s, hs, θy, ⟨min_le_right _ _, le_max_right _ _⟩, rfl⟩)

/-! ## Separation from inner points -/

lemma legL_sep_inner {r R T θx : ℝ} {p q : ℂ} (hr : 0 < r) (hR : 0 < R) (hRr : 500 * R ≤ r)
    (hT : |T| ≤ r / 2) (hT5 : |T - 5 * R| ≤ r / 2) (hp : p ∈ legL r R T θx)
    (hq : ‖q‖ ≤ 11 / 10 * r) (hqre : T + 2 * R ≤ q.re) : R ≤ dist p q := by
  rcases legL_cases hr hR.le hRr hT hT5 hp with ⟨hre, -, -⟩ | ⟨s, hs, rfl⟩ | ⟨φ, -, rfl⟩ |
    ⟨s, hs, rfl⟩
  · have hpre : p.re ≤ T - 2 * R := by rcases hre with ⟨-, -, h⟩ | h <;> linarith
    have := dist_ge_re p q
    rw [abs_of_nonpos (by linarith)] at this
    linarith
  · exact rad_inner_sep hr (foot_cos hr hT5) hs.1 hq
      (by rw [abs_of_nonpos (by linarith)]; linarith)
  · exact (dist_comm _ _).trans_ge (norm_sepR hq (by rw [norm_polPt (by linarith)])
      (by linarith))
  · exact (dist_comm _ _).trans_ge (norm_sepR (b := 5 / 4 * r) hq (by rw [norm_polPt (by linarith [hs.1])]; exact hs.1)
      (by linarith))

lemma legR_sep_inner {r R T' θy : ℝ} {p q : ℂ} (hr : 0 < r) (hR : 0 < R) (hRr : 500 * R ≤ r)
    (hT : |T'| ≤ r / 2) (hT5 : |T' + 5 * R| ≤ r / 2) (hp : p ∈ legR r R T' θy)
    (hq : ‖q‖ ≤ 11 / 10 * r) (hqre : q.re ≤ T' - 2 * R) : R ≤ dist p q := by
  rcases legR_cases hr hR.le hRr hT hT5 hp with ⟨hre, -, -⟩ | ⟨s, hs, rfl⟩ |
    ⟨s, hs, φ, -, rfl⟩
  · have hpre : T' + 2 * R ≤ p.re := by rcases hre with ⟨-, h, -⟩ | h <;> linarith
    have := dist_ge_re p q
    rw [abs_of_nonneg (by linarith)] at this
    linarith
  · exact rad_inner_sep hr (foot_cos hr hT5) hs.1 hq
      (by rw [abs_of_nonneg (by linarith)]; linarith)
  · exact (dist_comm _ _).trans_ge (norm_sepR (b := 7 / 4 * r) hq (by rw [norm_polPt (by linarith [hs.1])]; exact hs.1)
      (by linarith))

/-! ## `L̂_x` vs `L̂_y` -/

/-- the angular hypotheses: `θx` avoids the band of the window, `θy` avoids `θx` -/
theorem legL_legR_sep {r R T T' θx θy : ℝ} {p q : ℂ} (hr : 0 < r) (hR : 0 < R)
    (hRr : 500 * R ≤ r) (hT : |T| ≤ r / 2) (hT5 : |T - 5 * R| ≤ r / 2) (hT' : |T'| ≤ r / 2)
    (hT5' : |T' + 5 * R| ≤ r / 2) (hTT : T ≤ T')
    (hx1 : gA r R T + kap r R ≤ θx) (hx2 : θx ≤ gB r R T' + 2 * π - kap r R)
    (hy1 : θx - 2 * π + kap r R ≤ θy) (hy2 : θy ≤ θx - kap r R)
    (hp : p ∈ legL r R T θx) (hq : q ∈ legR r R T' θy) : R ≤ dist p q := by
  have hρ : (0 : ℝ) < 11 / 10 * r := by positivity
  have hab : gB r R T' + kap r R ≤ gA r R T := by
    have h := arccos_sub_ge (x := (T - 5 * R) / (11 / 10 * r)) (y := (T' + 5 * R) / (11 / 10 * r))
      (by rw [le_div_iff₀ hρ]; linarith [(abs_le.1 hT5).1])
      (by rw [div_le_iff₀ hρ]; linarith [(abs_le.1 hT5').2])
      (div_le_div_of_nonneg_right (by linarith) hρ.le)
    have e : (T' + 5 * R) / (11 / 10 * r) - (T - 5 * R) / (11 / 10 * r) =
        kap r R + (T' - T) / (11 / 10 * r) := by unfold kap; field_simp; ring
    have : 0 ≤ (T' - T) / (11 / 10 * r) := div_nonneg (by linarith) hρ.le
    unfold gA gB; linarith
  have hgA : gA r R T ≤ π := Real.arccos_le_pi _
  have hgB : 0 ≤ gB r R T' := Real.arccos_nonneg _
  have hk := kap_pos hr hR
  rcases legL_cases hr hR.le hRr hT hT5 hp with ⟨hre, -, hpn⟩ | ⟨s, hs, rfl⟩ |
    ⟨φ, hφ, rfl⟩ | ⟨s, hs, rfl⟩
  · rw [dist_comm]
    refine legR_sep_inner hr hR hRr hT' hT5' hq hpn ?_
    rcases hre with ⟨-, -, h⟩ | h <;> linarith
  all_goals
    rcases legR_cases hr hR.le hRr hT' hT5' hq with ⟨hre, -, hqn⟩ | ⟨s', hs', rfl⟩ |
      ⟨s', hs', φ', hφ', rfl⟩
    · refine legL_sep_inner hr hR hRr hT hT5 (by assumption) hqn ?_
      rcases hre with ⟨-, h, -⟩ | h <;> linarith
  · rw [dist_comm]
    exact angle_sepR hr hR hRr hs'.1 hs.1 (by linarith) (by linarith)
  · exact norm_sepR (a := 5 / 4 * r) (b := 7 / 4 * r) (by rw [norm_polPt (by linarith [hs.1])]; exact hs.2)
      (by rw [norm_polPt (by linarith [hs'.1])]; exact hs'.1) (by linarith)
  · rw [dist_comm]
    exact angle_sepR hr hR hRr hs'.1 (by linarith) (by linarith [hφ.1]) (by linarith [hφ.2])
  · exact norm_sepR (a := 5 / 4 * r) (b := 7 / 4 * r) (by rw [norm_polPt (by linarith)])
      (by rw [norm_polPt (by linarith [hs'.1])]; exact hs'.1) (by linarith)
  · rw [dist_comm]
    exact angle_sepR hr hR hRr hs'.1 (by linarith [hs.1]) (by linarith) (by linarith)
  · have h1 : θx - 2 * π + kap r R ≤ φ' := le_trans (le_min (by linarith) hy1) hφ'.1
    have h2 : φ' ≤ θx - kap r R := le_trans hφ'.2 (max_le (by linarith) hy2)
    rw [dist_comm]
    exact angle_sepR hr hR hRr (by linarith [hs'.1]) (by linarith [hs.1]) (by linarith)
      (by linarith)

end LQGMetric.GM
