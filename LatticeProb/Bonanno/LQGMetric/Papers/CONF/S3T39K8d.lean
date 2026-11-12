/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K8d at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K8c
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J1

/-!
# CONF Theorem 3.9, packet J6d, node O2: measurability of the lexicographic minimum

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1586 (the centre `x_{k,i}` is selected as the lexicographically smallest admissible point,
`t39jLexMin`, S3T39J1). **`k8_lexMin_meas`**: if a compact-nonempty-set-valued map `F` (on a class
`C ⊆ X`) has measurable hit events of open sets, then `t39jLexMin ∘ F` agrees on `C` with a
measurable map. The two coordinates are countable infima of rational thresholds
(`k8_einf`); for the second one the hit events of `{re < a, im < b'}` with rational
`a ↓ min re` are used (compactness). Own elementary argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric MeasureTheory Filter Topology

namespace LQGMetric.CONF

open Classical in

/-- a real number as the infimum of the rational thresholds above it -/
theorem k8_einf (v : ℝ) (P : ℚ → Prop) (hP : ∀ b : ℚ, P b ↔ v < b) :
    (⨅ b : ℚ, (if P b then ((b : ℝ) : EReal) else ⊤)) = (v : EReal) := by
  classical
  refine le_antisymm ?_ (le_iInf fun b => ?_)
  · by_contra hlt
    push_neg at hlt
    obtain ⟨a, ha₁, ha₂⟩ := EReal.lt_iff_exists_rat_btwn.1 hlt
    have hva : v < a := by exact_mod_cast ha₁
    have := iInf_le (fun b : ℚ => if P b then ((b : ℝ) : EReal) else ⊤) a
    rw [if_pos ((hP a).2 hva)] at this
    exact absurd (lt_of_le_of_lt this ha₂) (lt_irrefl _)
  · split_ifs with h
    · exact_mod_cast ((hP b).1 h).le
    · exact le_top

open Classical in
/-- the measurable function attached to rational thresholds -/
def k8Inf {X : Type*} (S : ℚ → Set X) (x : X) : ℝ :=
  EReal.toReal (⨅ b : ℚ, if x ∈ S b then ((b : ℝ) : EReal) else ⊤)

theorem k8Inf_meas {X : Type*} [MeasurableSpace X] {S : ℚ → Set X}
    (hS : ∀ b, MeasurableSet (S b)) : Measurable (k8Inf S) := by
  classical
  refine measurable_ereal_toReal.comp (Measurable.iInf fun b : ℚ => ?_)
  exact Measurable.ite (hS b) measurable_const measurable_const

theorem k8Inf_eq {X : Type*} {S : ℚ → Set X} {x : X} {v : ℝ} (hP : ∀ b : ℚ, x ∈ S b ↔ v < b) :
    k8Inf S x = v := by
  classical
  unfold k8Inf
  have := k8_einf v (fun b => x ∈ S b) hP
  rw [this]; rfl

/-- **the lexicographic minimum of a set-valued map with measurable hit events is measurable** -/
theorem k8_lexMin_meas {X : Type*} [MeasurableSpace X] (C : Set X) (F : X → Set ℂ)
    (hF : ∀ x ∈ C, IsCompact (F x) ∧ (F x).Nonempty) (H : Set ℂ → Set X)
    (hH : ∀ U, IsOpen U → MeasurableSet (H U))
    (hHF : ∀ U, IsOpen U → ∀ x ∈ C, ((F x ∩ U).Nonempty ↔ x ∈ H U)) :
    ∃ Ψ : X → ℂ, Measurable Ψ ∧ ∀ x ∈ C, t39jLexMin (F x) = Ψ x := by
  have hore : ∀ a : ℝ, IsOpen {z : ℂ | z.re < a} := fun a =>
    isOpen_lt Complex.continuous_re continuous_const
  set S₁ : ℚ → Set X := fun a => H {z | z.re < a}
  set m₁ := k8Inf S₁
  have hm₁ : Measurable m₁ := k8Inf_meas fun a => hH _ (hore _)
  -- first coordinate
  have hμ : ∀ x ∈ C, m₁ x = sInf (Complex.re '' F x) := by
    intro x hx
    obtain ⟨hc, hne⟩ := hF x hx
    refine k8Inf_eq fun a => ?_
    rw [← hHF _ (hore _) x hx]
    have hmem := (hc.image Complex.continuous_re).sInf_mem (hne.image _)
    have hbdd := (hc.image Complex.continuous_re).bddBelow
    constructor
    · rintro ⟨z, hz, hza⟩
      exact lt_of_le_of_lt (csInf_le hbdd ⟨z, hz, rfl⟩) hza
    · intro h
      obtain ⟨z, hz, hze⟩ := hmem
      exact ⟨z, hz, by simp only [mem_ofPred_eq]; rw [hze]; exact h⟩
  have hoV : ∀ a b : ℝ, IsOpen {z : ℂ | z.re < a ∧ z.im < b} := fun a b =>
    (hore a).inter (isOpen_lt Complex.continuous_im continuous_const)
  set S₂ : ℚ → Set X := fun b => ⋃ b' : ℚ, ⋃ (_ : b' < b), ⋂ j : ℕ, ⋃ a : ℚ,
    {x | m₁ x < a ∧ (a : ℝ) < m₁ x + 1 / ((j : ℝ) + 1)} ∩ H {z | z.re < a ∧ z.im < b'}
  have hS₂ : ∀ b, MeasurableSet (S₂ b) := fun b =>
    MeasurableSet.iUnion fun b' => MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun j =>
      MeasurableSet.iUnion fun a => ((measurableSet_lt hm₁ measurable_const).inter
        (measurableSet_lt measurable_const (hm₁.add measurable_const))).inter (hH _ (hoV _ _))
  set m₂ := k8Inf S₂
  have hm₂ : Measurable m₂ := k8Inf_meas hS₂
  refine ⟨fun x => (m₁ x : ℂ) + (m₂ x : ℂ) * Complex.I,
    (Complex.measurable_ofReal.comp hm₁).add
      ((Complex.measurable_ofReal.comp hm₂).mul measurable_const), fun x hx => ?_⟩
  obtain ⟨hc, hne⟩ := hF x hx
  set μ := sInf (Complex.re '' F x) with hμdef
  have hμx := hμ x hx
  have hbdd := (hc.image Complex.continuous_re).bddBelow
  have hle : ∀ z ∈ F x, μ ≤ z.re := fun z hz => csInf_le hbdd ⟨z, hz, rfl⟩
  have hF₁c : IsCompact (F x ∩ {z | z.re = μ}) :=
    hc.inter_right (isClosed_eq Complex.continuous_re continuous_const)
  have hF₁n : (F x ∩ {z | z.re = μ}).Nonempty := by
    obtain ⟨z, hz, hze⟩ := (hc.image Complex.continuous_re).sInf_mem (hne.image _)
    exact ⟨z, hz, hze⟩
  set ν := sInf (Complex.im '' (F x ∩ {z | z.re = μ})) with hνdef
  have hbdd₂ := (hF₁c.image Complex.continuous_im).bddBelow
  have hm₂x : m₂ x = ν := by
    refine k8Inf_eq fun b => ?_
    simp only [S₂, mem_iUnion, mem_iInter, mem_inter_iff, mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨b', hb', hj⟩
      have : ∀ j : ℕ, ∃ z ∈ F x, z.re < μ + 1 / ((j : ℝ) + 1) ∧ z.im < b' := by
        intro j
        obtain ⟨a, ⟨-, ha⟩, hH'⟩ := hj j
        obtain ⟨z, hz, hz1, hz2⟩ := (hHF _ (hoV _ _) x hx).2 hH'
        rw [hμx] at ha
        exact ⟨z, hz, by linarith [show z.re < (a : ℝ) from hz1], hz2⟩
      choose z hz hz1 hz2 using this
      obtain ⟨z₀, hz₀, φ, hφ, hlim⟩ := hc.tendsto_subseq hz
      have hre : z₀.re ≤ μ := by
        refine le_of_forall_pos_lt_add fun ε hε => ?_
        obtain ⟨j₀, hj₀⟩ := exists_nat_one_div_lt (half_pos hε)
        have hlim' := (Complex.continuous_re.tendsto z₀).comp hlim
        obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.1 hlim') (ε / 2) (half_pos hε)
        have h1 := hk (max k j₀) (le_max_left _ _)
        have h2 := hz1 (φ (max k j₀))
        have h3 : 1 / ((φ (max k j₀) : ℝ) + 1) ≤ 1 / ((j₀ : ℝ) + 1) := by
          gcongr; exact_mod_cast (le_max_right k j₀).trans (hφ.id_le _)
        rw [Real.dist_eq, abs_lt] at h1
        simp only [Function.comp] at h1
        linarith [h1.1]
      have him : z₀.im ≤ b' := le_of_tendsto' ((Complex.continuous_im.tendsto z₀).comp hlim)
        fun k => (hz2 (φ k)).le
      have hz₀μ : z₀.re = μ := le_antisymm hre (hle z₀ hz₀)
      have := csInf_le hbdd₂ ⟨z₀, ⟨hz₀, hz₀μ⟩, rfl⟩
      exact_mod_cast lt_of_le_of_lt (this.trans him) (by exact_mod_cast hb')
    · intro hνb
      obtain ⟨z, ⟨hz, hzμ⟩, hzν⟩ := (hF₁c.image Complex.continuous_im).sInf_mem (hF₁n.image _)
      obtain ⟨b', hb'₁, hb'₂⟩ := exists_rat_btwn hνb
      refine ⟨b', by exact_mod_cast hb'₂, fun j => ?_⟩
      have hj0 : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn (show μ < μ + 1 / ((j : ℝ) + 1) by linarith)
      refine ⟨a, ⟨by rw [hμx]; exact ha₁, by rw [hμx]; exact ha₂⟩, ?_⟩
      refine (hHF _ (hoV _ _) x hx).1 ⟨z, hz, ?_, ?_⟩
      · simp only [mem_ofPred_eq] at hzμ; rw [hzμ]; exact ha₁
      · rw [hzν]; exact hb'₁
  simp only
  rw [hμx, hm₂x]
  apply Complex.ext <;> simp [t39jLexMin, hμdef, hνdef]

end LQGMetric.CONF
