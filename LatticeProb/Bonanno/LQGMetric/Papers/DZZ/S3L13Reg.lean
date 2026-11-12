/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L13Reg at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13Sel
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13Meas
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentWN

/-!
# DZZ Lemma 3.13: space-time regions of the fine field and of the box masses (P2-DZZ313)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1314–1340. The white noise read by
`η^{s_B}_{δ'}(x)` lives in `(δ'², s_B²) × B(x, r(·))` and the one read by `M_{γ,s_b}(b)` in
`(s_b², ∞) × B(c_b, r(·))` (DZZ (eq:WND_decomposition-approximation), l. 440–446). Here:

* `fineReg l`, `boxReg b`: these regions; `supportedIn_etaKernelL2_reg` (kernel support).
* `L313Q`: the requirements on the box sequence of Lemma 3.13 together with the geometric content of
  (Eq.fine-field-independent): every box explored by the partition reads white noise disjoint from the
  fine field of the sequence. `L313QMin` (shortest such sequences), `l313Sel` (the selected one).
* `measurable_l313Q`, `disjoint_of_l313Sel_eq`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox KilledHeat

/-- The white-noise region of a band kernel: the kernel `etaKernelL2 I w` vanishes outside
`{(s, z) : s ∈ I, z ∈ B(w, r(s))}`. -/
theorem supportedIn_etaKernelL2_reg {I : Set ℝ} (hI : MeasurableSet I) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hI0 : I ⊆ Ioi c₀) (w : ℂ) :
    SupportedIn {q : ℝ × ℂ | q.1 ∈ I ∧ q.2 ∈ Metric.ball w (etaRad q.1)} (etaKernelL2 I w) := by
  have hm := memLp_etaKernel hI hc₀ hI0 w
  have hA : MeasurableSet {q : ℝ × ℂ | q.1 ∈ I ∧ q.2 ∈ Metric.ball w (etaRad q.1)} :=
    (measurable_fst hI).inter (measurableSet_lt ((continuous_dist.comp
      (continuous_snd.prodMk continuous_const)).measurable) (measurable_etaRad.comp measurable_fst))
  unfold SupportedIn
  rw [etaKernelL2, dite_eq_left_of_eq_true (eq_true hm)]
  rw [ae_restrict_iff' hA.compl]
  filter_upwards [hm.coeFn_toLp] with p hp hpA
  rw [hp]
  by_cases h1 : p.1 ∈ I
  · simp only [etaKernel, indicator_of_mem h1]
    have h2 : p.2 ∉ Metric.ball w (etaRad p.1) := fun h2 => hpA ⟨h1, h2⟩
    have hp0 : (p.1 / 2).toNNReal ≠ 0 := by
      have := hI0 h1
      simp only [mem_Ioi] at this
      simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; linarith
    refine killedHeat_eq_zero_of_not_mem_right
      (LQGMetric.isOpen_openSquare.inter Metric.isOpen_ball) hp0 _ ?_
    intro hm2
    exact h2 hm2.2
  · simp [etaKernel, indicator_of_notMem h1]

/-- The region of the fine field `{η^{s_B}_{δ'}(x) : δ' < s_B, x ∈ B_large, B ∈ l}`. -/
def fineReg (l : List DyBox) : Set (ℝ × ℂ) :=
  {q | ∃ b ∈ l, ∃ x ∈ b.largeBox, q.1 ∈ Ioo 0 (b.side ^ 2) ∧ q.2 ∈ Metric.ball x (etaRad q.1)}

/-- The region read by `M_{γ, s_b}(b)` (through `η_{s_b}(c_b)`). -/
def boxReg (b : DyBox) : Set (ℝ × ℂ) :=
  {q | q.1 ∈ Ioi (b.side ^ 2) ∧ q.2 ∈ Metric.ball b.center (etaRad q.1)}

@[simp] lemma fineReg_nil : fineReg [] = ∅ := by
  ext q; simp [fineReg]

lemma side_pos' (b : DyBox) : 0 < b.side := by unfold DyBox.side; positivity

lemma supportedIn_boxKer (b : DyBox) :
    SupportedIn (boxReg b) (etaKernelL2 (Ioi (b.side ^ 2)) b.center) :=
  supportedIn_etaKernelL2_reg measurableSet_Ioi (pow_pos (side_pos' b) 2) subset_rfl _

/-- **Requirements on the box sequence** (DZZ Lemma 3.13 and (Eq.fine-field-independent)), for the
cell predicate `c` of `𝒱_δ`: neighbouring boxes joining `u`, `v`, each inside a cell `𝖢` with
`s_B = s_𝖢 ε²`, and every box explored by the partition reads white noise disjoint from the fine field
of the sequence. -/
def L313Q (ε : ℝ) (u v : ℂ) (c : DyBox → Prop) (l : List DyBox) : Prop :=
  ((∃ hl : l ≠ [], (l.head hl).Mem u ∧ (l.getLast hl).Mem v) ∧ l.IsChain Neighbour) ∧
    (∀ b ∈ l, ∃ C : DyBox, c C ∧ b.closedBox ⊆ C.closedBox ∧ b.side = C.side * ε ^ 2) ∧
    ∀ b', Explored c b' → Disjoint (boxReg b') (fineReg l)

/-- An injective key on box sequences (for the deterministic tie-break). -/
def listKey : List DyBox → ℕ := (Encodable.ofCountable (List DyBox)).encode

lemma listKey_injective : Function.Injective listKey :=
  @Encodable.encode_injective _ (Encodable.ofCountable (List DyBox))

lemma measurable_l313Q (ε : ℝ) (u v : ℂ) (l : List DyBox) :
    Measurable fun c : DyBox → Prop => L313Q ε u v c l := by
  unfold L313Q Explored
  refine measurable_const.and (Measurable.and ?_ ?_)
  · exact Measurable.forall fun b => measurable_const.imp
      (Measurable.exists fun C => (measurable_pi_apply C).and measurable_const)
  · exact Measurable.forall fun b' => (Measurable.forall fun i =>
      measurable_const.imp (measurable_pi_apply _).not).imp measurable_const

end DZZ
end LQGMetric
