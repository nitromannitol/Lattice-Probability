/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.LGDMeas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L8

/-!
# ω-measurability of DZZ's Liouville graph distance (P2-LGDMEAS)

DZZ (Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 121–124) take expectations of
`log D_{γ,δ}(u,v)` (Lemma 2.12, l. 740–759; (eq-very-crude), l. 849–853; Lemma 3.10) without
commenting on measurability. Here we prove it (own elementary argument, AGENT_GUIDE cost rule):

* `lgdMinSet_eq_lgdRat`: the radii in `lgdDZZ` may be taken rational. The path image is compact,
  so it is already covered by the balls shrunk by a factor `1 - 1/(n+2)` for one `n`
  (`IsCompact.elim_directed_cover`), and a rational radius in between keeps the mass `≤ δ²`
  (monotonicity of `μ`). So `D` is a function `lgdRat` of the countable family of ball masses
  `μ(B(c,q))`, `c ∈ ℚ²`, `q ∈ ℚ`.
* `measurable_lgdRat`: `{lgdRat ≤ K}` is a countable union of finite intersections of the events
  `{μ(B(c,q)) ≤ δ²}`; the covering condition is deterministic.
* `measurable_lgdDZZ`, `aemeasurable_lgdDZZ`, `measurable_lgdMinSet`, `aemeasurable_lgdMinSet`,
  and the `Real.log (·).toNat` versions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- the deterministic covering condition on rational data: the union of the balls `B(c_i, q_i)`
contains a path from a point of `A` to a point of `B` -/
def ratCov (A B : Set ℂ) (N : ℕ) (c : Fin N → ℚ × ℚ) (q : Fin N → ℚ) : Prop :=
  ∃ x ∈ A, ∃ y ∈ B, ∃ P : Path x y, ∀ t, ∃ i, P t ∈ Metric.ball (ratPt (c i)) (q i)

/-- `N` balls with rational data are admissible for the mass function `m` -/
def ratAdm (m : ℚ × ℚ → ℚ → ℝ≥0∞) (δ : ℝ) (A B : Set ℂ) (N : ℕ) : Prop :=
  ∃ (c : Fin N → ℚ × ℚ) (q : Fin N → ℚ), ratCov A B N c q ∧
    ∀ i, 0 < q i ∧ m (c i) (q i) ≤ ENNReal.ofReal (δ ^ 2)

/-- the Liouville graph distance as a function of the rational ball masses `m c q = μ(B(c,q))` -/
def lgdRat (m : ℚ × ℚ → ℚ → ℝ≥0∞) (δ : ℝ) (A B : Set ℂ) : ℕ∞ :=
  ⨅ (N : ℕ) (_ : ratAdm m δ A B N), (N : ℕ∞)

/-- the rational ball masses of `μ` -/
def ballMassQ (μ : Measure ℂ) : ℚ × ℚ → ℚ → ℝ≥0∞ :=
  fun c q => μ (Metric.ball (ratPt c) q)

/-- the shrinking factor `1 - 1/(n+2)` is monotone -/
lemma shrinkFac_mono : Monotone fun n : ℕ => 1 - 1 / ((n : ℝ) + 2) := by
  intro a b hab
  have : 1 / ((b : ℝ) + 2) ≤ 1 / ((a : ℝ) + 2) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 2)
  simp only; linarith

/-- **radii may be taken rational**: a cover of a path by `N` open balls can be replaced by a
cover by `N` concentric balls with rational radii `0 < q_i ≤ ρ_i`. -/
lemma exists_rat_radii {x y : ℂ} (P : Path x y) {N : ℕ} (c : Fin N → ℂ) (ρ : Fin N → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hcov : ∀ t, ∃ i, P t ∈ Metric.ball (c i) (ρ i)) :
    ∃ q : Fin N → ℚ, (∀ i, 0 < q i ∧ (q i : ℝ) ≤ ρ i) ∧
      ∀ t, ∃ i, P t ∈ Metric.ball (c i) (q i) := by
  set r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2) with hr
  have hr0 : ∀ n, 0 < r n := fun n => by
    have : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; have := n.cast_nonneg (α := ℝ); linarith
    simp only [hr]; linarith
  have hr1 : ∀ n, r n < 1 := fun n => by
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    simp only [hr]; linarith
  set U : ℕ → Set ℂ := fun n => ⋃ i, Metric.ball (c i) (ρ i * r n) with hU
  obtain ⟨n, hn⟩ := (isCompact_range P.continuous).elim_directed_cover U
    (fun n => isOpen_iUnion fun i => Metric.isOpen_ball) (by
      rintro _ ⟨t, rfl⟩
      obtain ⟨i, hi⟩ := hcov t
      rw [Metric.mem_ball] at hi
      have hpos : 0 < 1 - dist (P t) (c i) / ρ i := by
        rw [sub_pos, div_lt_one (hρ i)]; exact hi
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      refine mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨i, Metric.mem_ball.2 ?_⟩⟩
      have h2 : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h3 : dist (P t) (c i) / ρ i < r n := by simp only [hr]; linarith
      rwa [div_lt_iff₀ (hρ i), mul_comm] at h3)
    (by
      intro a b
      refine ⟨max a b, ?_, ?_⟩ <;>
      · refine iUnion_mono fun i => Metric.ball_subset_ball ?_
        exact mul_le_mul_of_nonneg_left (shrinkFac_mono (by omega)) (hρ i).le)
  have hq : ∀ i, ∃ q : ℚ, ρ i * r n < q ∧ (q : ℝ) < ρ i := fun i =>
    exists_rat_btwn (by nlinarith [hρ i, hr1 n])
  choose q hq1 hq2 using hq
  refine ⟨q, fun i => ⟨?_, (hq2 i).le⟩, fun t => ?_⟩
  · have : (0 : ℝ) < q i := lt_trans (mul_pos (hρ i) (hr0 n)) (hq1 i)
    exact_mod_cast this
  · obtain ⟨i, hi⟩ := mem_iUnion.1 (hn ⟨t, rfl⟩)
    exact ⟨i, Metric.ball_subset_ball (hq1 i).le hi⟩

/-- `min_{A×B} D_δ` is `lgdRat` of the rational ball masses -/
theorem lgdMinSet_eq_lgdRat (μ : Measure ℂ) (δ : ℝ) (A B : Set ℂ) :
    lgdMinSet μ δ A B = lgdRat (ballMassQ μ) δ A B := by
  unfold lgdMinSet lgdRat
  refine le_antisymm ?_ ?_
  · refine le_iInf₂ fun N hN => ?_
    obtain ⟨c, q, ⟨x, hx, y, hy, P, hP⟩, hm⟩ := hN
    refine (iInf₂_le x hx).trans ((iInf₂_le y hy).trans ?_)
    unfold lgdDZZ
    exact iInf₂_le N ⟨c, fun i => q i, P, fun i => ⟨show (0 : ℝ) < q i by exact_mod_cast (hm i).1, (hm i).2⟩, hP⟩
  · refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    unfold lgdDZZ
    refine le_iInf₂ fun N hN => ?_
    obtain ⟨c, ρ, P, h1, h2⟩ := hN
    obtain ⟨q, hq, hcov⟩ := exists_rat_radii P (fun i => ratPt (c i)) ρ (fun i => (h1 i).1) h2
    refine iInf₂_le N ⟨c, q, ⟨x, hx, y, hy, P, hcov⟩, fun i => ⟨(hq i).1, ?_⟩⟩
    exact (measure_mono (Metric.ball_subset_ball (hq i).2)).trans (h1 i).2

/-- `D_δ(u,v)` is `lgdRat` of the rational ball masses -/
theorem lgdDZZ_eq_lgdRat (μ : Measure ℂ) (δ : ℝ) (u v : ℂ) :
    lgdDZZ μ δ u v = lgdRat (ballMassQ μ) δ {u} {v} := by
  rw [← lgdMinSet_eq_lgdRat]
  simp [lgdMinSet]

/-- sublevel sets of `lgdRat` -/
lemma lgdRat_le_iff (m : ℚ × ℚ → ℚ → ℝ≥0∞) (δ : ℝ) (A B : Set ℂ) (K : ℕ) :
    lgdRat m δ A B ≤ K ↔ ∃ N, ratAdm m δ A B N ∧ N ≤ K := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have : ((K + 1 : ℕ) : ℕ∞) ≤ lgdRat m δ A B :=
      le_iInf₂ fun N hN => by exact_mod_cast hne N hN
    have := this.trans h
    norm_cast at this
    omega
  · rintro ⟨N, hN, hNK⟩
    exact (iInf₂_le N hN).trans (by exact_mod_cast hNK)

/-- an `ℕ∞`-valued map is measurable once its finite sublevel sets are -/
lemma measurable_enat_of_le {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℕ∞}
    (hf : ∀ K : ℕ, MeasurableSet {ω | f ω ≤ K}) : Measurable f := by
  refine measurable_to_countable' fun k => ?_
  induction k using ENat.recTopCoe with
  | top =>
    have : f ⁻¹' {⊤} = (⋃ K : ℕ, {ω | f ω ≤ K})ᶜ := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, mem_iUnion, mem_ofPred_eq,
        not_exists]
      constructor
      · intro h K; rw [h]; exact not_le.2 (ENat.natCast_lt_top K)
      · intro h
        induction hω : f ω using ENat.recTopCoe with
        | top => rfl
        | coe n => exact absurd (le_of_eq hω) (h n)
    rw [this]; exact (MeasurableSet.iUnion hf).compl
  | coe k =>
    have : f ⁻¹' {(k : ℕ∞)} = {ω | f ω ≤ k} ∩ ⋂ j : Fin k, {ω | f ω ≤ (j : ℕ)}ᶜ := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_iInter, mem_compl_iff,
        mem_ofPred_eq]
      induction f ω using ENat.recTopCoe with
      | top => simp
      | coe n =>
        simp only [Nat.cast_inj, Nat.cast_le]
        constructor
        · rintro rfl; exact ⟨le_rfl, fun j => by have := j.2; omega⟩
        · rintro ⟨h1, h2⟩
          by_contra hne
          exact h2 ⟨n, by omega⟩ le_rfl
    rw [this]
    exact (hf k).inter (MeasurableSet.iInter fun j => (hf j).compl)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **measurability of `lgdRat`** in the ball masses -/
theorem measurable_lgdRat {m : Ω → ℚ × ℚ → ℚ → ℝ≥0∞} (hm : ∀ c q, Measurable fun ω => m ω c q)
    (δ : ℝ) (A B : Set ℂ) : Measurable fun ω => lgdRat (m ω) δ A B := by
  refine measurable_enat_of_le fun K => ?_
  simp_rw [lgdRat_le_iff, ratAdm]
  refine measurableSet_setOfPred.2 (Measurable.exists fun N => Measurable.and
    (Measurable.exists fun c => Measurable.exists fun q => Measurable.and measurable_const
      (Measurable.forall fun i => Measurable.and measurable_const
        (measurableSet_setOfPred.1 (measurableSet_le (hm _ _) measurable_const))))
    measurable_const)

theorem aemeasurable_lgdRat {P : Measure Ω} {m : Ω → ℚ × ℚ → ℚ → ℝ≥0∞}
    (hm : ∀ c q, AEMeasurable (fun ω => m ω c q) P) (δ : ℝ) (A B : Set ℂ) :
    AEMeasurable (fun ω => lgdRat (m ω) δ A B) P := by
  have hae : ∀ᵐ ω ∂P, ∀ c q, m ω c q = (hm c q).mk _ ω :=
    ae_all_iff.2 fun c => ae_all_iff.2 fun q => (hm c q).ae_eq_mk
  refine ⟨fun ω => lgdRat (fun c q => (hm c q).mk _ ω) δ A B,
    measurable_lgdRat (fun c q => (hm c q).measurable_mk) δ A B, ?_⟩
  filter_upwards [hae] with ω hω
  congr 1
  funext c q
  exact hω c q

theorem aemeasurable_lgdDZZ {P : Measure Ω} {μ : Ω → Measure ℂ}
    (hμ : ∀ c r, AEMeasurable (fun ω => μ ω (Metric.ball c r)) P) (δ : ℝ) (u v : ℂ) :
    AEMeasurable (fun ω => lgdDZZ (μ ω) δ u v) P := by
  simp_rw [lgdDZZ_eq_lgdRat]
  exact aemeasurable_lgdRat (fun c q => hμ _ _) δ _ _

theorem aemeasurable_lgdMinSet {P : Measure Ω} {μ : Ω → Measure ℂ}
    (hμ : ∀ c r, AEMeasurable (fun ω => μ ω (Metric.ball c r)) P) (δ : ℝ) (A B : Set ℂ) :
    AEMeasurable (fun ω => lgdMinSet (μ ω) δ A B) P := by
  simp_rw [lgdMinSet_eq_lgdRat]
  exact aemeasurable_lgdRat (fun c q => hμ _ _) δ _ _

/-- any function of an `ℕ∞`-valued (a.e.-)measurable map is (a.e.-)measurable -/
lemma measurable_log_toNat : Measurable fun k : ℕ∞ => Real.log (k.toNat : ℝ) :=
  Measurable.of_discrete

theorem aemeasurable_log_lgdDZZ {P : Measure Ω} {μ : Ω → Measure ℂ}
    (hμ : ∀ c r, AEMeasurable (fun ω => μ ω (Metric.ball c r)) P) (δ : ℝ) (u v : ℂ) :
    AEMeasurable (fun ω => Real.log ((lgdDZZ (μ ω) δ u v).toNat : ℝ)) P :=
  measurable_log_toNat.comp_aemeasurable (aemeasurable_lgdDZZ hμ δ u v)

theorem aemeasurable_log_lgdMinSet {P : Measure Ω} {μ : Ω → Measure ℂ}
    (hμ : ∀ c r, AEMeasurable (fun ω => μ ω (Metric.ball c r)) P) (δ : ℝ) (A B : Set ℂ) :
    AEMeasurable (fun ω => Real.log ((lgdMinSet (μ ω) δ A B).toNat : ℝ)) P :=
  measurable_log_toNat.comp_aemeasurable (aemeasurable_lgdMinSet hμ δ A B)

end DZZ
end LQGMetric
