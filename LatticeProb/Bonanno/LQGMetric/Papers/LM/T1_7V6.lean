/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V3

/-!
# LM Theorem 1.7, packet P-VAR (d): joint measurability of the square metrics in `(θ, D)`

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Theorem 1.7 (l. 1000–1036): `θ` is uniform on `[0,1]²` and
independent of `(h, D)`, and the internal metrics `{D(·,·;S) : S ∈ 𝒮^ε_θ}` are random variables of
`(θ, D)`. For the Tonelli arguments over `θ` (LM Lemma 5.2, D107 §1.3) we need the coordinates
`t17Y ε θ s D` (the chain formula `chainInf` on the squares, evaluated on the dense pairs) to be
jointly Borel in `(θ, D)`.

The only `V`-dependent ingredient of `chainInf V` is `bdDist V x = D(x, Vᶜ) = inf_{y ∉ V} D(x, y)`.
For the open square `S_θ` the complement is the closure of the open set `t17Out ε θ k` ("strictly
outside the closed square"), so by continuity of `D(x, ·)`
`D(x, S_θᶜ) = inf_n {D(x, q_n) : q_n ∈ t17Out ε θ k}` (dense sequence `q`), and the conditions
`q_n ∈ t17Out ε θ k` are open in `θ`. Own elementary argument (no source needed: standard).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric.LM

/-- the points strictly outside the closed square `cl S_k` -/
def t17Out (ε : ℝ) (θ : ℝ × ℝ) (k : ℤ × ℤ) : Set ℂ :=
  {y | y.re < ε * (k.1 + θ.1) ∨ ε * (k.1 + 1 + θ.1) < y.re ∨ y.im < ε * (k.2 + θ.2) ∨
    ε * (k.2 + 1 + θ.2) < y.im}

lemma t17v_isOpen_out (ε : ℝ) (θ : ℝ × ℝ) (k : ℤ × ℤ) : IsOpen (t17Out ε θ k) :=
  (isOpen_lt Complex.continuous_re continuous_const).union
    ((isOpen_lt continuous_const Complex.continuous_re).union
    ((isOpen_lt Complex.continuous_im continuous_const).union
    (isOpen_lt continuous_const Complex.continuous_im)))

lemma t17v_out_sub (ε : ℝ) (θ : ℝ × ℝ) (k : ℤ × ℤ) : t17Out ε θ k ⊆ (t17Square ε θ k)ᶜ := by
  rintro y hy ⟨h1, h2, h3, h4⟩
  rcases hy with h | h | h | h <;> linarith

lemma t17v_compl_sub_closure (ε : ℝ) (θ : ℝ × ℝ) (k : ℤ × ℤ) :
    (t17Square ε θ k)ᶜ ⊆ closure (t17Out ε θ k) := by
  intro y hy
  rw [Metric.mem_closure_iff]
  intro r hr
  simp only [t17Square, mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_lt] at hy
  have hr2 : (0 : ℝ) < r / 2 := by positivity
  have hd : ∀ u : ℂ, ‖u‖ = r / 2 → dist y (y + u) < r := fun u hu => by
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, hu]; linarith
  rcases hy with h | h | h | h
  · refine ⟨y + ((-(r / 2) : ℝ) : ℂ), Or.inl ?_, hd _ (by simp [hr.le])⟩
    simp only [Complex.add_re, Complex.ofReal_re]; linarith
  · refine ⟨y + ((r / 2 : ℝ) : ℂ), Or.inr (Or.inl ?_), hd _ (by simp [hr.le])⟩
    simp only [Complex.add_re, Complex.ofReal_re]; linarith
  · refine ⟨y + ((-(r / 2) : ℝ) : ℂ) * Complex.I, Or.inr (Or.inr (Or.inl ?_)),
      hd _ (by simp [hr.le])⟩
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]; linarith
  · refine ⟨y + ((r / 2 : ℝ) : ℂ) * Complex.I, Or.inr (Or.inr (Or.inr ?_)),
      hd _ (by simp [hr.le])⟩
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]; linarith

open scoped Classical in
/-- the countable formula for `D(x, S_θᶜ)` -/
theorem t17v_bdDist_eq (d : ContMetric) (ε : ℝ) (θ : ℝ × ℝ) (k : ℤ × ℤ) (x : ℂ) :
    d.bdDist (t17Square ε θ k) x = ⨅ n : ℕ, if TopologicalSpace.denseSeq ℂ n ∈ t17Out ε θ k
      then ENNReal.ofReal (d.1 (x, TopologicalSpace.denseSeq ℂ n)) else ⊤ := by
  set q := TopologicalSpace.denseSeq ℂ
  rw [ContMetric.bdDist_eq]
  refine le_antisymm (le_iInf fun n => ?_) (le_iInf₂ fun y hy => ?_)
  · split_ifs with h
    · exact biInf_le (fun y => ENNReal.ofReal (d.1 (x, y))) (t17v_out_sub ε θ k h)
    · exact le_top
  · have hg : Continuous fun y : ℂ => ENNReal.ofReal (d.1 (x, y)) :=
      ENNReal.continuous_ofReal.comp (d.1.continuous.comp (continuous_const.prodMk continuous_id))
    have hcl : closure (t17Out ε θ k) ⊆ closure (t17Out ε θ k ∩ range q) :=
      closure_minimal ((TopologicalSpace.denseRange_denseSeq ℂ).open_subset_closure_inter
        (t17v_isOpen_out ε θ k)) isClosed_closure
    have hC : IsClosed {y : ℂ | (⨅ n : ℕ, if q n ∈ t17Out ε θ k
        then ENNReal.ofReal (d.1 (x, q n)) else ⊤) ≤ ENNReal.ofReal (d.1 (x, y))} :=
      isClosed_le continuous_const hg
    refine closure_minimal (fun u hu => ?_) hC (hcl (t17v_compl_sub_closure ε θ k hy))
    obtain ⟨hu1, n, rfl⟩ := hu
    refine (iInf_le (fun n : ℕ => if q n ∈ t17Out ε θ k
      then ENNReal.ofReal (d.1 (x, q n)) else ⊤) n).trans ?_
    rw [if_pos hu1]

lemma t17v_measurableSet_out (ε : ℝ) (k : ℤ × ℤ) (y : ℂ) :
    MeasurableSet {θ : ℝ × ℝ | y ∈ t17Out ε θ k} := by
  have hc1 : Continuous fun θ : ℝ × ℝ => ε * (k.1 + θ.1) := by fun_prop
  have hc2 : Continuous fun θ : ℝ × ℝ => ε * (k.1 + 1 + θ.1) := by fun_prop
  have hc3 : Continuous fun θ : ℝ × ℝ => ε * (k.2 + θ.2) := by fun_prop
  have hc4 : Continuous fun θ : ℝ × ℝ => ε * (k.2 + 1 + θ.2) := by fun_prop
  exact (measurableSet_lt measurable_const hc1.measurable).union
    ((measurableSet_lt hc2.measurable measurable_const).union
    ((measurableSet_lt measurable_const hc3.measurable).union
    (measurableSet_lt hc4.measurable measurable_const)))

open scoped Classical in
/-- `(θ, D) ↦ D(x, S_θᶜ)` is Borel -/
theorem t17v_measurable_bdDist (ε : ℝ) (k : ℤ × ℤ) (x : ℂ) :
    Measurable fun p : (ℝ × ℝ) × ContMetric => p.2.bdDist (t17Square ε p.1 k) x := by
  simp_rw [t17v_bdDist_eq]
  refine Measurable.iInf fun n => Measurable.ite ?_ ?_ measurable_const
  · exact measurable_fst (t17v_measurableSet_out ε k _)
  · exact (ENNReal.measurable_ofReal.comp ((continuous_eval_const _).measurable.comp measurable_subtype_coe)).comp measurable_snd

theorem t17v_measurable_chainStep (ε : ℝ) (k : ℤ × ℤ) (x y : ℂ) :
    Measurable fun p : (ℝ × ℝ) × ContMetric => p.2.chainStep (t17Square ε p.1 k) x y := by
  have he : Measurable fun p : (ℝ × ℝ) × ContMetric => edist (p.2.pt x) (p.2.pt y) := by
    simp_rw [ContMetric.edist_pt]
    exact (ENNReal.measurable_ofReal.comp ((continuous_eval_const _).measurable.comp measurable_subtype_coe)).comp measurable_snd
  unfold ContMetric.chainStep
  exact Measurable.ite (measurableSet_lt he (t17v_measurable_bdDist ε k x)) he measurable_const

theorem t17v_measurable_chainVal (ε : ℝ) (k : ℤ × ℤ) (l : List ℂ) :
    ∀ x y : ℂ, Measurable fun p : (ℝ × ℝ) × ContMetric =>
      p.2.chainVal (t17Square ε p.1 k) x l y := by
  induction l with
  | nil => exact fun x y => t17v_measurable_chainStep ε k x y
  | cons a l ih =>
    intro x y
    simp only [ContMetric.chainVal]
    exact (t17v_measurable_chainStep ε k x a).add (ih a y)

/-- `(θ, D) ↦ D(z, w; S_θ)` (chain formula) is Borel -/
theorem t17v_measurable_chainInf (ε : ℝ) (k : ℤ × ℤ) (z w : ℂ) :
    Measurable fun p : (ℝ × ℝ) × ContMetric => p.2.chainInf (t17Square ε p.1 k) z w :=
  Measurable.iInf fun _ => t17v_measurable_chainVal ε k _ z w

/-- **the square coordinates are jointly Borel in `(θ, D)`** -/
theorem t17v_measurable_Y (ε : ℝ) (s : Finset (ℤ × ℤ)) :
    Measurable fun p : (ℝ × ℝ) × ContMetric => t17Y ε p.1 s p.2 :=
  measurable_pi_iff.2 fun k => measurable_pi_iff.2 fun _ =>
    t17v_measurable_chainInf ε k _ _

end LQGMetric.LM
