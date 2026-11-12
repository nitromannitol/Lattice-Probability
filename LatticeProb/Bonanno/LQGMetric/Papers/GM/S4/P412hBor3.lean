/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412hBor3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412hBor2

/-!
# `gd(K, y)` is Borel (D98 §2, packet P-L414Borel, part 3)

Source: decision D98 §2; own descriptive-set-theory argument (GM do not discuss measurability).

For a regular random closed set `K` (`P412hRC`) and a measurable point `y`, the events
`{gd(K x, y x) = q}` agree, on `{K x compact connected with connected complement}`, with Borel
sets (**`p412h_meas_gd`**). Ingredients: the radius index `p412hNf` is measurable
(`p412h_measurable_nf`); at a fixed radius the admissibility (`p412hOKr`) and maximality
(`p412hMxr`, via the comparison `p412h_bs_sub_iff`) are Borel; `gd` is a least-index choice.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Topology Bornology
open LQGMetric.Topo.Crosscut LQGMetric.LocalEvent

namespace LQGMetric.GM

open Classical in
/-- the index of the radius `ρ` -/
def p412hNf (K : Set ℂ) (y : ℂ) (ε : ℝ) : ℕ :=
  if h : ∃ j, p412hRhoOK K y ε j then Nat.find h else 0

theorem p412h_rho_nf (K : Set ℂ) (y : ℂ) (ε : ℝ) :
    p412hRho K y ε = p412hRad ε (p412hNf K y ε) := by
  unfold p412hRho p412hNf
  split_ifs
  · rfl
  · simp only [p412hRad, Nat.cast_zero, zero_add, mul_one]; ring

/-- admissibility at a fixed radius `r` -/
def p412hOKr (K : Set ℂ) (y : ℂ) (ε r : ℝ) (i : ℕ) : Prop :=
  (p412hIx i).1 ∈ p412hT K ε ∧ p412hArc K y r (p412hC ε i) (p412hY ε r i)

/-- maximality at a fixed radius `r` -/
def p412hMxr (K : Set ℂ) (y : ℂ) (ε r : ℝ) (i : ℕ) : Prop :=
  p412hOKr K y ε r i ∧ ∀ j, p412hOKr K y ε r j →
    p412hBs K r (p412hC ε i) (p412hY ε r i) ⊆ p412hBs K r (p412hC ε j) (p412hY ε r j) →
    p412hBs K r (p412hC ε j) (p412hY ε r j) ⊆ p412hBs K r (p412hC ε i) (p412hY ε r i)

theorem p412h_Mx_iff (K : Set ℂ) (y : ℂ) (ε : ℝ) (i : ℕ) :
    p412hMx K y ε i ↔ p412hMxr K y ε (p412hRad ε (p412hNf K y ε)) i := by
  unfold p412hMx p412hMxr p412hOK p412hOKr
  rw [p412h_rho_nf]

theorem p412h_gd_iff (K : Set ℂ) (y : ℂ) (ε : ℝ) (q : ℂ) :
    p412hGd K y ε = q ↔ (∃ i, p412hMx K y ε i ∧ (∀ i' < i, ¬ p412hMx K y ε i') ∧
      p412hC ε i = q) ∨ ((∀ i, ¬ p412hMx K y ε i) ∧ p412hG ε (0, 0) = q) := by
  classical
  unfold p412hGd
  split_ifs with h
  · constructor
    · intro he
      exact Or.inl ⟨Nat.find h, Nat.find_spec h, fun i' hi' => Nat.find_min h hi', he⟩
    · rintro (⟨i, hi, hmin, hq⟩ | ⟨hn, -⟩)
      · rw [(Nat.find_eq_iff h).2 ⟨hi, hmin⟩]; exact hq
      · exact absurd (Nat.find_spec h) (hn _)
  · constructor
    · intro he; exact Or.inr ⟨fun i hi => h ⟨i, hi⟩, he⟩
    · rintro (⟨i, hi, -⟩ | ⟨-, hq⟩)
      · exact absurd ⟨i, hi⟩ h
      · exact hq

variable {X : Type} [MeasurableSpace X] {K : X → Set ℂ}

theorem p412h_meas_T (hK : P412hRC K) (ε : ℝ) (m : ℤ × ℤ) :
    MeasurableSet {x | m ∈ p412hT (K x) ε} := by
  have e : {x | m ∈ p412hT (K x) ε} =
      {x | Disjoint (closedBall (p412hG ε m) (3 * ε + ε / 8)) (K x)}ᶜ := by
    ext x
    simp only [p412hT, mem_ofPred_eq, mem_compl_iff, not_disjoint_iff_nonempty_inter]
  rw [e]; exact (p412h_meas_disj hK (isCompact_closedBall _ _)).compl

theorem p412h_meas_rhoOK (hK : P412hRC K) {y : X → ℂ} (hy : Measurable y) (ε : ℝ) (j : ℕ) :
    MeasurableSet {x | p412hRhoOK (K x) (y x) ε j} := by
  have e : {x | p412hRhoOK (K x) (y x) ε j} = ⋂ m : ℤ × ℤ,
      ({x | m ∈ p412hT (K x) ε}ᶜ ∪ {x | dist (y x) (p412hG ε m) ≠ p412hRad ε j}) := by
    ext x
    simp only [p412hRhoOK, mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, imp_iff_not_or]
  rw [e]
  exact MeasurableSet.iInter fun m => (p412h_meas_T hK ε m).compl.union
    (measurableSet_eq_fun (hy.dist measurable_const) measurable_const).compl

theorem p412h_measurable_nf (hK : P412hRC K) {y : X → ℂ} (hy : Measurable y) (ε : ℝ) :
    Measurable fun x => p412hNf (K x) (y x) ε := by
  classical
  refine measurable_to_countable' fun j => ?_
  have e : (fun x => p412hNf (K x) (y x) ε) ⁻¹' {j} =
      ({x | p412hRhoOK (K x) (y x) ε j} ∩ ⋂ i : ℕ, ⋂ (_ : i < j),
        {x | p412hRhoOK (K x) (y x) ε i}ᶜ) ∪
      ((⋂ i : ℕ, {x | p412hRhoOK (K x) (y x) ε i}ᶜ) ∩ {_x | j = 0}) := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_ofPred_eq,
      mem_iInter, mem_compl_iff, p412hNf]
    split_ifs with h
    · rw [Nat.find_eq_iff]
      constructor
      · intro hj; exact Or.inl hj
      · rintro (hj | ⟨hn, -⟩)
        · exact hj
        · exact absurd (Nat.find_spec h) (hn _)
    · push Not at h
      constructor
      · intro hj; exact Or.inr ⟨h, hj.symm⟩
      · rintro (⟨hj, -⟩ | ⟨-, hj⟩)
        · exact absurd hj (h j)
        · exact hj.symm
  rw [e]
  exact ((p412h_meas_rhoOK hK hy ε j).inter (MeasurableSet.iInter fun i => MeasurableSet.iInter
    fun _ => (p412h_meas_rhoOK hK hy ε i).compl)).union
    ((MeasurableSet.iInter fun i => (p412h_meas_rhoOK hK hy ε i).compl).inter
      (MeasurableSet.const _))

theorem p412h_Y_mem (ε : ℝ) {r : ℝ} (hr : 0 ≤ r) (i : ℕ) :
    p412hY ε r i ∈ sphere (p412hC ε i) r := p412h_pt_mem _ hr _

theorem p412h_meas_OKr (hK : P412hRC K) {y : X → ℂ} (hy : Measurable y) (ε : ℝ) {r : ℝ}
    (hr : 0 < r) (i : ℕ) : MeasurableSet {x | p412hOKr (K x) (y x) ε r i} := by
  have hY := p412h_Y_mem ε hr.le i
  exact (p412h_meas_T hK ε _).inter ((MeasurableSet.const _).inter ((hK.mem _).compl.inter
    ((p412h_meas_arcN hK hr hY).inter (p412h_meas_arcY hK hr hY hy))))

/-- the comparison set of `p412h_bs_sub_iff` -/
def p412hEr (K : Set ℂ) (ε r : ℝ) (i j : ℕ) : Prop :=
  (∃ k : ℕ, qd k ∈ p412hBs K r (p412hC ε i) (p412hY ε r i) ∧
      qd k ∈ p412hBs K r (p412hC ε j) (p412hY ε r j)) ∧
    ∀ θ : ℚ, p412hPt (p412hC ε j) r θ ∈
        connectedComponentIn (sphere (p412hC ε j) r \ K) (p412hY ε r j) →
      p412hPt (p412hC ε j) r θ ∉ p412hBs K r (p412hC ε i) (p412hY ε r i)

theorem p412h_meas_Er (hK : P412hRC K) (ε : ℝ) {r : ℝ} (hr : 0 < r) (i j : ℕ) :
    MeasurableSet {x | p412hEr (K x) ε r i j} := by
  have hYi := p412h_Y_mem ε hr.le i
  have hYj := p412h_Y_mem ε hr.le j
  have hBi := p412h_meas_dgB (p412h_ct_arc hK hr hYi)
  have hBj := p412h_meas_dgB (p412h_ct_arc hK hr hYj)
  have e : {x | p412hEr (K x) ε r i j} = (⋃ k : ℕ,
      ({x | qd k ∈ p412hBs (K x) r (p412hC ε i) (p412hY ε r i)} ∩
        {x | qd k ∈ p412hBs (K x) r (p412hC ε j) (p412hY ε r j)})) ∩ ⋂ θ : ℚ,
      ({x | p412hPt (p412hC ε j) r θ ∈
        connectedComponentIn (sphere (p412hC ε j) r \ K x) (p412hY ε r j)}ᶜ ∪
       {x | p412hPt (p412hC ε j) r θ ∈ p412hBs (K x) r (p412hC ε i) (p412hY ε r i)}ᶜ) := by
    ext x
    simp only [p412hEr, mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter, mem_union,
      mem_compl_iff, imp_iff_not_or]
  rw [e]
  exact (MeasurableSet.iUnion fun k => (hBi _).inter (hBj _)).inter
    (MeasurableSet.iInter fun θ => (p412h_meas_arc hK hr hYj).compl.union (hBi _).compl)

/-- the geometric hypotheses of L4.14 on `K` -/
def p412hGeo (K : Set ℂ) : Prop := IsCompact K ∧ IsConnected K ∧ IsPreconnected Kᶜ

theorem p412h_sub_iff_Er {K : Set ℂ} (hK : p412hGeo K) {y : ℂ} {ε r : ℝ} (hr : 0 < r) {i j : ℕ}
    (hi : p412hOKr K y ε r i) :
    p412hBs K r (p412hC ε i) (p412hY ε r i) ⊆ p412hBs K r (p412hC ε j) (p412hY ε r j) ↔
      p412hEr K ε r i j :=
  p412h_bs_sub_iff hK.1 hK.2.1 hK.2.2 hr hi.2.1 hi.2.2.1 (closure_nonempty_iff.1 ⟨y, hi.2.2.2.2⟩)

/-- the Borel set representing `p412hMxr` -/
def p412hMset (K : X → Set ℂ) (y : X → ℂ) (ε r : ℝ) (i : ℕ) : Set X :=
  {x | p412hOKr (K x) (y x) ε r i} ∩ ⋂ j : ℕ, ({x | p412hOKr (K x) (y x) ε r j}ᶜ ∪
    {x | p412hEr (K x) ε r i j}ᶜ ∪ {x | p412hEr (K x) ε r j i})

theorem p412h_meas_Mset (hK : P412hRC K) {y : X → ℂ} (hy : Measurable y) (ε : ℝ) {r : ℝ}
    (hr : 0 < r) (i : ℕ) : MeasurableSet (p412hMset K y ε r i) :=
  (p412h_meas_OKr hK hy ε hr i).inter (MeasurableSet.iInter fun j =>
    ((p412h_meas_OKr hK hy ε hr j).compl.union (p412h_meas_Er hK ε hr i j).compl).union
      (p412h_meas_Er hK ε hr j i))

theorem p412h_Mxr_iff {y : X → ℂ} {ε r : ℝ} (hr : 0 < r) {x : X} (hx : p412hGeo (K x)) (i : ℕ) :
    p412hMxr (K x) (y x) ε r i ↔ x ∈ p412hMset K y ε r i := by
  simp only [p412hMxr, p412hMset, mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_union,
    mem_compl_iff]
  constructor
  · rintro ⟨hi, H⟩
    refine ⟨hi, fun j => ?_⟩
    by_cases hj : p412hOKr (K x) (y x) ε r j
    · by_cases hE : p412hEr (K x) ε r i j
      · exact Or.inr ((p412h_sub_iff_Er hx hr hj).1 (H j hj ((p412h_sub_iff_Er hx hr hi).2 hE)))
      · exact Or.inl (Or.inr hE)
    · exact Or.inl (Or.inl hj)
  · rintro ⟨hi, H⟩
    refine ⟨hi, fun j hj hsub => ?_⟩
    rcases H j with (h | h) | h
    · exact absurd hj h
    · exact absurd ((p412h_sub_iff_Er hx hr hi).1 hsub) h
    · exact (p412h_sub_iff_Er hx hr hj).2 h

/-- **`gd` is Borel** (D98 §2): on `{K x compact, connected, with connected complement}`,
`{gd(K x, y x) = q}` agrees with a Borel set -/
theorem p412h_meas_gd (hK : P412hRC K) {y : X → ℂ} (hy : Measurable y) {ε : ℝ} (hε : 0 < ε)
    (q : ℂ) : ∃ E : Set X, MeasurableSet E ∧
      ∀ x, p412hGeo (K x) → (p412hGd (K x) (y x) ε = q ↔ x ∈ E) := by
  have hr : ∀ j, 0 < p412hRad ε j := fun j => by linarith [(p412h_rad_mem hε j).1]
  set M : ℕ → Set X := fun i => ⋃ j : ℕ,
    ((fun x => p412hNf (K x) (y x) ε) ⁻¹' {j} ∩ p412hMset K y ε (p412hRad ε j) i) with hMdef
  have hMm : ∀ i, MeasurableSet (M i) := fun i => MeasurableSet.iUnion fun j =>
    ((p412h_measurable_nf hK hy ε) (measurableSet_singleton j)).inter
      (p412h_meas_Mset hK hy ε (hr j) i)
  have hM : ∀ x, p412hGeo (K x) → ∀ i, (p412hMx (K x) (y x) ε i ↔ x ∈ M i) := by
    intro x hx i
    rw [p412h_Mx_iff, p412h_Mxr_iff (hr _) hx]
    simp only [hMdef, mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨j, hj, h⟩ => hj ▸ h⟩
  refine ⟨(⋃ i : ℕ, (M i ∩ (⋂ i' : ℕ, ⋂ (_ : i' < i), (M i')ᶜ) ∩ {_x | p412hC ε i = q})) ∪
    ((⋂ i : ℕ, (M i)ᶜ) ∩ {_x | p412hG ε (0, 0) = q}), ?_, fun x hx => ?_⟩
  · exact (MeasurableSet.iUnion fun i => ((hMm i).inter (MeasurableSet.iInter fun i' =>
      MeasurableSet.iInter fun _ => (hMm i').compl)).inter (MeasurableSet.const _)).union
      ((MeasurableSet.iInter fun i => (hMm i).compl).inter (MeasurableSet.const _))
  rw [p412h_gd_iff]
  simp only [mem_union, mem_iUnion, mem_inter_iff, mem_iInter, mem_compl_iff, mem_ofPred_eq,
    hM x hx, and_assoc]

end LQGMetric.GM
