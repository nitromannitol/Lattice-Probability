/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18A

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.18 (`Blueprint.DGProp3_21`) from its square version

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.18
(`prop-lfpp-upper`, statement DG:1603–1610), DG:1774–1779: "Proposition 3.22 implies the analogous
statement with `𝕊` replaced with any other square `S ⊂ ℂ` (with the rate of convergence of the
probability depending on the square). Lemma 2.2 then implies that the same is true with a
whole-plane GFF in place of a zero-boundary GFF on `S(1)`. We obtain the proposition statement
from this by covering `K` by a finite union of squares `S` such that `S(1/2)` is contained in
`U`."

* `DGProp3_18Sq` — the intermediate statement of DG:1774–1777 (the first two sentences): for the
  whole-plane field and *every* square `S` (centre `c`, half side `r`; `S(1/2)` has half side
  `2r`), w.p. `≥ 1 − Cδ^p`, `max_{z,w∈S} D^δ(z,w;S(1/2)) ≤ δ^{λ−ζ}`; constants depend on the
  square only (DG: "with the rate … depending on the square").
* `dgProp3_21_of : DGProp3_18Sq → Blueprint.DGProp3_21` — DG's third sentence: covering of `K`
  by finitely many squares and chaining inside the connected `U` (S3P18A), union bound.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

/-- **DG Prop 3.22 transferred to every square and to the whole-plane GFF** (DG:1774–1777). -/
def DGProp3_18Sq : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (c : ℂ) (r : ℝ), 0 < r →
    ∀ ζ ∈ Ioo (0 : ℝ) 1, ∃ p C δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (hc : ℝ → ℂ → Ω → ℝ),
        LQGDimension.IsGFFCircleAverage hc P → ∀ δ ∈ Ioo (0 : ℝ) δ₀,
          P {ω | ¬ ∀ z ∈ t18Sq c r, ∀ w ∈ t18Sq c r,
            dgLFPP (xiGamma γ) (fun x => hc δ x ω) (t18Sq c (2 * r)) z w ≤
              δ ^ (dgLambda γ - ζ)} ≤ ENNReal.ofReal (C * δ ^ p)

lemma t18_finset_consts {ι : Type} (Q : Finset ι) (p δ₀ : ι → ℝ) (hp : ∀ i ∈ Q, 0 < p i)
    (hδ : ∀ i ∈ Q, 0 < δ₀ i) :
    ∃ p' δ' : ℝ, 0 < p' ∧ 0 < δ' ∧ ∀ i ∈ Q, p' ≤ p i ∧ δ' ≤ δ₀ i := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨1, 1, one_pos, one_pos, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨p', δ', hp', hδ', hle⟩ := ih (fun i hi => hp i (Finset.mem_insert_of_mem hi))
      (fun i hi => hδ i (Finset.mem_insert_of_mem hi))
    refine ⟨min (p a) p', min (δ₀ a) δ', lt_min (hp a (Finset.mem_insert_self _ _)) hp',
      lt_min (hδ a (Finset.mem_insert_self _ _)) hδ', fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨min_le_left _ _, min_le_left _ _⟩
    · exact ⟨(min_le_right _ _).trans (hle i hi).1, (min_le_right _ _).trans (hle i hi).2⟩

/-- one more hop at the end of a chain `x₀ ⇄ x` -/
lemma t18_star {U : Set ℂ} {x₀ x z : ℂ} {s : ℝ} (hs : 0 < s) (hsU : closedBall x (4 * s) ⊆ U)
    (hzx : ‖z - x‖ ≤ s) {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) {M : ℝ} {n : ℕ}
    (hg : T18Good ξ φ M (x, s)) (p₁ : ∃ q, IsDGPath (closure U) x₀ x q)
    (p₂ : ∃ q, IsDGPath (closure U) x x₀ q) (b₁ : dgLFPP ξ φ (closure U) x₀ x ≤ n * M)
    (b₂ : dgLFPP ξ φ (closure U) x x₀ ≤ n * M) :
    (∃ q, IsDGPath (closure U) x₀ z q) ∧ (∃ q, IsDGPath (closure U) z x₀ q) ∧
      dgLFPP ξ φ (closure U) x₀ z ≤ (n + 1) * M ∧ dgLFPP ξ φ (closure U) z x₀ ≤ (n + 1) * M := by
  obtain ⟨ha, hb, hsub, hs2⟩ := t18_hop_geom hs hsU hzx
  have cv := t18Sq_convex x (2 * s)
  have sg₁ := t18_isDGPath_segment cv (hs2 ha) (hs2 hb)
  have sg₂ := t18_isDGPath_segment cv (hs2 hb) (hs2 ha)
  have up : ∀ {a b : ℂ} {q : ℝ → ℂ}, IsDGPath (t18Sq x (2 * s)) a b q →
      IsDGPath (closure U) a b q := fun hq =>
    ⟨hq.source, hq.target, hq.mapsTo.mono_right hsub, hq.continuousOn, hq.piecewise_contDiff⟩
  obtain ⟨q₁, hq₁⟩ := p₁
  obtain ⟨q₂, hq₂⟩ := p₂
  have h3 := (t15_dgLFPP_mono hsub ⟨_, sg₁⟩).trans (hg x ha z hb)
  have h4 := (t15_dgLFPP_mono hsub ⟨_, sg₂⟩).trans (hg z hb x ha)
  refine ⟨⟨_, t18_isDGPath_concat hq₁ (up sg₁)⟩, ⟨_, t18_isDGPath_concat (up sg₂) hq₂⟩,
    (t18_dgLFPP_triangle hφ ⟨_, hq₁⟩ ⟨_, up sg₁⟩).trans (by linarith),
    (t18_dgLFPP_triangle hφ ⟨_, up sg₂⟩ ⟨_, hq₂⟩).trans (by linarith)⟩

/-- `A δ^{λ−ζ/2} ≤ δ^{λ−ζ}` for `δ ≤ (A⁻¹)^{2/ζ}` -/
lemma t18_absorb {A δ ζ lam : ℝ} (hA : 1 ≤ A) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδA : δ ≤ A⁻¹ ^ (2 / ζ)) : A * δ ^ (lam - ζ / 2) ≤ δ ^ (lam - ζ) := by
  have hA0 : 0 < A := by linarith
  have h1 : δ ^ (ζ / 2) ≤ A⁻¹ := by
    calc δ ^ (ζ / 2) ≤ (A⁻¹ ^ (2 / ζ)) ^ (ζ / 2) :=
          Real.rpow_le_rpow hδ.le hδA (by positivity)
      _ = A⁻¹ := by
          rw [← Real.rpow_mul (by positivity), show 2 / ζ * (ζ / 2) = 1 by field_simp,
            Real.rpow_one]
  have h2 : δ ^ (lam - ζ / 2) = δ ^ (lam - ζ) * δ ^ (ζ / 2) := by
    rw [← Real.rpow_add hδ]; ring_nf
  rw [h2]
  calc A * (δ ^ (lam - ζ) * δ ^ (ζ / 2)) ≤ A * (δ ^ (lam - ζ) * A⁻¹) := by
        gcongr
    _ = δ ^ (lam - ζ) := by field_simp

/-- **DG Proposition 3.18** (`Blueprint.DGProp3_21`, DG:1603–1610) from its square version
(DG:1774–1779). -/
theorem dgProp3_21_of (hsq : DGProp3_18Sq) : Blueprint.DGProp3_21 := by
  classical
  intro γ hγ hγ2 U K hU hUc hK hKU ζ hζ
  rcases K.eq_empty_or_nonempty with hKe | ⟨x₀, hx₀⟩
  · refine ⟨1, 0, 1, one_pos, one_pos, fun P hc _ δ _ => ?_⟩
    have : {ω | ¬ dgDiam (xiGamma γ) (fun x => hc δ x ω) U K ≤
        ENNReal.ofReal (δ ^ (dgLambda γ - ζ))} = ∅ := by
      ext ω; simp [dgDiam, hKe]
    rw [this, measure_empty]; exact bot_le
  have hcov : ∀ x ∈ K, ∃ s : ℝ, 0 < s ∧ closedBall x (4 * s) ⊆ U := fun x hx => by
    obtain ⟨r, hr, hrU⟩ := isOpen_iff.1 hU x (hKU hx)
    exact ⟨r / 8, by positivity, (closedBall_subset_ball (by linarith)).trans hrU⟩
  choose! s hs hsU using hcov
  obtain ⟨F, hFK, hKF⟩ := hK.elim_nhds_subcover (fun x => ball x (s x))
    (fun x hx => ball_mem_nhds x (hs x hx))
  have hch := fun x (hx : x ∈ F) => t18_chain (hKU hx₀)
    (t18_reflTransGen_hop hU hUc (hKU hx₀) (hKU (hFK x hx)))
  choose! Qf nf hQf hp₁ hp₂ hbf using hch
  set Q : Finset (ℂ × ℝ) := F.image (fun x => (x, s x)) ∪ F.biUnion Qf with hQdef
  have hQ : ∀ q ∈ Q, 0 < q.2 := by
    intro q hq
    rcases Finset.mem_union.1 hq with hq | hq
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hq
      exact hs x (hFK x hx)
    · obtain ⟨x, hx, hq⟩ := Finset.mem_biUnion.1 hq
      exact (hQf x hx q hq).1
  have hζ2 : ζ / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hζ.1], by linarith [hζ.2]⟩
  have hq := fun q (hq : q ∈ Q) => hsq γ hγ hγ2 q.1 q.2 (hQ q hq) (ζ / 2) hζ2
  choose! pq Cq dq hpq hdq hbq using hq
  obtain ⟨p', δ', hp', hδ', hle⟩ := t18_finset_consts Q pq dq hpq hdq
  set N : ℕ := F.sup nf
  set A : ℝ := 2 * N + 2
  have hA : 1 ≤ A := by have : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith
  set δ₁ := min (min δ' 1) (A⁻¹ ^ (2 / ζ))
  have hδ₁ : 0 < δ₁ := lt_min (lt_min hδ' one_pos) (by positivity)
  refine ⟨p', ∑ q ∈ Q, |Cq q|, δ₁, hp', hδ₁, fun {Ω} _ P hc hG δ hδ => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδ'' : δ < δ' := hδ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ1 : δ < 1 := hδ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδA : δ ≤ A⁻¹ ^ (2 / ζ) := hδ.2.le.trans (min_le_right _ _)
  set M := δ ^ (dgLambda γ - ζ / 2)
  have hM : 0 ≤ M := Real.rpow_nonneg hδ0.le _
  have hsub : {ω | ¬ dgDiam (xiGamma γ) (fun x => hc δ x ω) U K ≤
      ENNReal.ofReal (δ ^ (dgLambda γ - ζ))} ⊆
      ⋃ q ∈ Q, {ω | ¬ T18Good (xiGamma γ) (fun x => hc δ x ω) M q} := by
    intro ω hω
    by_contra hn
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_not] at hn
    apply hω
    have hφ : Continuous fun x => hc δ x ω := hG.continuous δ hδ0 ω
    have key : ∀ z ∈ K, ∃ n : ℕ, n ≤ N ∧ (∃ q, IsDGPath (closure U) x₀ z q) ∧
        (∃ q, IsDGPath (closure U) z x₀ q) ∧
        dgLFPP (xiGamma γ) (fun x => hc δ x ω) (closure U) x₀ z ≤ (n + 1) * M ∧
        dgLFPP (xiGamma γ) (fun x => hc δ x ω) (closure U) z x₀ ≤ (n + 1) * M := by
      intro z hz
      obtain ⟨x, hxF, hzx⟩ := mem_iUnion₂.1 (hKF hz)
      rw [mem_ball, dist_eq_norm] at hzx
      have hxK := hFK x hxF
      obtain ⟨b₁, b₂⟩ := hbf x hxF (xiGamma γ) _ hφ M hM fun q hq =>
        hn q (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨x, hxF, hq⟩))
      exact ⟨nf x, Finset.le_sup hxF, t18_star (hs x hxK) (hsU x hxK) hzx.le hφ
        (hn _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hxF))) (hp₁ x hxF)
        (hp₂ x hxF) b₁ b₂⟩
    refine iSup₂_le fun z hz => iSup₂_le fun w hw => ENNReal.ofReal_le_ofReal ?_
    obtain ⟨n, hn1, -, hz2, -, hz4⟩ := key z hz
    obtain ⟨m, hm1, hw1, -, hw3, -⟩ := key w hw
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn1
    have hmN : (m : ℝ) ≤ N := by exact_mod_cast hm1
    calc dgLFPP (xiGamma γ) (fun x => hc δ x ω) (closure U) z w
        ≤ dgLFPP (xiGamma γ) (fun x => hc δ x ω) (closure U) z x₀ +
          dgLFPP (xiGamma γ) (fun x => hc δ x ω) (closure U) x₀ w :=
          t18_dgLFPP_triangle hφ hz2 hw1
      _ ≤ (n + 1) * M + (m + 1) * M := add_le_add hz4 hw3
      _ ≤ A * M := by
          have : ((n : ℝ) + 1) * M + (m + 1) * M = (n + m + 2) * M := by ring
          rw [this]; exact mul_le_mul_of_nonneg_right (by linarith) hM
      _ ≤ δ ^ (dgLambda γ - ζ) := t18_absorb hA hζ.1 hδ0 hδA
  calc P {ω | ¬ dgDiam (xiGamma γ) (fun x => hc δ x ω) U K ≤
        ENNReal.ofReal (δ ^ (dgLambda γ - ζ))}
      ≤ P (⋃ q ∈ Q, {ω | ¬ T18Good (xiGamma γ) (fun x => hc δ x ω) M q}) := measure_mono hsub
    _ ≤ ∑ q ∈ Q, P {ω | ¬ T18Good (xiGamma γ) (fun x => hc δ x ω) M q} :=
        measure_biUnion_finset_le Q _
    _ ≤ ∑ q ∈ Q, ENNReal.ofReal (|Cq q| * δ ^ p') := by
        refine Finset.sum_le_sum fun q hq => ?_
        refine (hbq q hq P hc hG δ ⟨hδ0, hδ''.trans_le (hle q hq).2⟩).trans
          (ENNReal.ofReal_le_ofReal ?_)
        exact mul_le_mul (le_abs_self _)
          (Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (hle q hq).1)
          (Real.rpow_nonneg hδ0.le _) (abs_nonneg _)
    _ = ENNReal.ofReal ((∑ q ∈ Q, |Cq q|) * δ ^ p') := by
        rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun q _ =>
          mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hδ0.le _)]

end LQGMetric.DG
