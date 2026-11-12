/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K5j at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K5h
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanBasic

/-!
# CONF Theorem 3.9, packet J6d: fields 4–6 with the interior class (`(interior K).Nonempty`)

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1559–1561, 1586. Copies of `t39k5_fields_of_hit` (S3T39K5) and `t39k5_fields_at` (S3T39K5i,
D132-amended form, DEC-132 N5) in which the deterministic Effros-measurability inputs `hCtr`,
`hGood` are only required on the class of closed bounded `K` with **nonempty interior** and Jordan
frontier (the class for which `T39K8LocAccessI` is available without the separation half of the
Jordan curve theorem; handoff/P2-T39K8.md §6). All uses are filled metric balls
`𝓑^•_s(z₀; D_h)` with `s > 0`, which contain `z₀` in their interior
(`t39k5j_mem_interior_filledBall`: `z₀ ∈ 𝓑_s ⊆ int 𝓑^•_s`, `GM.jb_ballM_subset_interior`);
this is deterministic, so no new hypothesis appears in `t39k5_fields_atI`.

* `t39k5j_mem_interior_filledBall`: `0 < s → z₀ ∈ interior (filledBall d z₀ s)`;
* **`t39k5_fields_of_hitI`**: `t39k5_fields_of_hit` with the interior class, the good event
  strengthened by `z₀ ∈ int 𝓑^•_{s_k}`;
* **`t39k5_fields_atI`**: `t39k5_fields_at` with the interior class.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Function TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint LocalEvent GM

/-- the centre lies in the interior of a filled ball of positive radius:
`z₀ ∈ 𝓑_s(z₀; d) ⊆ int 𝓑^•_s(z₀; d)` -/
theorem t39k5j_mem_interior_filledBall (d : ContMetric) (z₀ : ℂ) {s : ℝ} (hs : 0 < s) :
    z₀ ∈ interior (filledBall d z₀ s) :=
  jb_ballM_subset_interior (jb_mem_ballM d z₀ s hs)

section Fields
variable {Ω : Type} [m0 : MeasurableSpace Ω] {P : Measure Ω}

/-- **`t39k5_fields_of_hit` with the interior class**: `hCtr`/`hGood` only on closed bounded `K`
with `(interior K).Nonempty` and Jordan frontier; the good event additionally contains
`z₀ ∈ int 𝓑^•_{s_k}` -/
theorem t39k5_fields_of_hitI (D : DistC → ContMetric) (h : Ω → DistC) (z₀ : ℂ) (R : ℝ)
    {ι : Type} [Fintype ι] (I₀ : ι → Ω → Set ℂ) (s : ℕ → Ω → ℝ) (k : ℕ)
    (hs : ∀ ω, 0 ≤ s k ω)
    (hhit : ∀ i, ∀ U : Set ℂ, IsOpen U →
      AEEventIn P (filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s k ω)))
        {ω | (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω) ∩ U).Nonempty})
    (hgood : ∀ᵐ ω ∂P, JordanMap.IsJordanCurve (frontier (filledBall (D (h ω)) z₀ (s k ω))) ∧
      Bornology.IsBounded (filledBall (D (h ω)) z₀ (s k ω)) ∧
      z₀ ∈ interior (filledBall (D (h ω)) z₀ (s k ω)))
    (hCtr : ∃ Ψ : ℝ → Set ℂ × Set ℂ → ℂ,
      (∀ r, @Measurable _ _ (@Prod.instMeasurableSpace _ _ effrosSigma effrosSigma) _ (Ψ r)) ∧
      ∀ (K J : Set ℂ) (r : ℝ), IsClosed K → Bornology.IsBounded K → (interior K).Nonempty →
        JordanMap.IsJordanCurve (frontier K) → J ⊆ frontier K → t39jCtr K J r = Ψ r (K, J))
    (hGood : ∃ A : ℕ → Set (Set ℂ × Set ℂ),
      (∀ q, MeasurableSet[@Prod.instMeasurableSpace _ _ effrosSigma effrosSigma] (A q)) ∧
      ∀ (K J : Set ℂ) (q : ℕ), IsClosed K → Bornology.IsBounded K → (interior K).Nonempty →
        JordanMap.IsJordanCurve (frontier K) → J ⊆ frontier K →
        (t39jGoodAct K J q R ↔ (K, J) ∈ A q)) :
    (∃ g : Ω → ℕ, Measurable[filledBallSigmaAt0 D h z₀
        (fun ω => ENNReal.ofReal (s k ω))] g ∧
      (fun ω => t39j7N D h z₀ I₀ (s k) ω) =ᵐ[P] g) ∧
    (∀ i, ∃ g : Ω → ℂ, Measurable[filledBallSigmaAt0 D h z₀
        (fun ω => ENNReal.ofReal (s k ω))] g ∧
      t39jX D h z₀ R I₀ s (fun k => t39j7N D h z₀ I₀ (s k)) k i =ᵐ[P] g) ∧
    (∀ i, AEEventIn P (filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s k ω)))
      (t39jAct D h z₀ R I₀ s (fun k => t39j7N D h z₀ I₀ (s k)) k i)) := by
  have hn := t39k5_hnm_of_hit (P := P) (D := D) (h := h) (z₀ := z₀) I₀ (s k)
    (fun i => by simpa using hhit i univ isOpen_univ)
  have hsub : ∀ i ω, t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω) ⊆
      frontier (filledBall (D (h ω)) z₀ (s k ω)) := fun _ _ _ hx => hx.1
  obtain ⟨Ψ, hΨm, hΨ⟩ := hCtr
  obtain ⟨A, hAm, hA⟩ := hGood
  refine ⟨hn, fun i => ?_, fun i => ?_⟩
  · obtain ⟨G, hG, hGe⟩ := t39k5_comp_ae (fun q p => Ψ ((2 : ℝ)⁻¹ ^ t39gExp q * R / 2) p)
      (fun q => hΨm _) (fun ω => filledBall (D (h ω)) z₀ (s k ω))
      (fun ω => t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)) (fun ω => t39j7N D h z₀ I₀ (s k) ω)
      (fun U hU => t39k5_fb_hit D h z₀ hs hU) (hhit i) hn
    refine ⟨G, hG, Filter.EventuallyEq.trans ?_ hGe⟩
    filter_upwards [hgood] with ω hω
    exact hΨ _ _ _ (gm_filledBall_isClosed _ _ _) hω.2.1 ⟨z₀, hω.2.2⟩ hω.1 (hsub i ω)
  · obtain ⟨F, hF, hEF⟩ := t39k5_comp_aeEventIn A hAm
      (fun ω => filledBall (D (h ω)) z₀ (s k ω))
      (fun ω => t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)) (fun ω => t39j7N D h z₀ I₀ (s k) ω)
      (fun U hU => t39k5_fb_hit D h z₀ hs hU) (hhit i) hn
    refine ⟨F, hF, Filter.EventuallyEq.trans ?_ hEF⟩
    filter_upwards [hgood] with ω hω
    exact propext (hA _ _ _ (gm_filledBall_isClosed _ _ _) hω.2.1 ⟨z₀, hω.2.2⟩ hω.1 (hsub i ω))

end Fields

/-- **`t39k5_fields_at` with the interior class** (D132-amended form: `harcs`, `harcsM`);
`hCtr`/`hGood` only on closed bounded `K` with `(interior K).Nonempty` and Jordan frontier. The
extra good-event clause `z₀ ∈ int 𝓑^•_{s_k}` follows from `0 < τ ≤ s_k`. -/
theorem t39k5_fields_atI (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (z₀ : ℂ) (R : ℝ) {ι : Type} [Fintype ι]
    (arcs : ι → Set ℂ → Set ℂ) (τ : Ω → ℝ) (I₀ : ι → Ω → Set ℂ)
    (hI₀ : ∀ i ω, I₀ i ω = arcs i (frontier (filledBall (D (h ω)) z₀ (τ ω))))
    (s : ℕ → Ω → ℝ) (k : ℕ) (hs : ∀ ω, 0 ≤ s k ω)
    (hgood : ∀ᵐ ω ∂P, 0 < τ ω ∧ τ ω ≤ s k ω ∧
      Bornology.IsBounded (filledBall (D (h ω)) z₀ (s k ω)) ∧
      JordanMap.IsJordanCurve (frontier (filledBall (D (h ω)) z₀ (s k ω))))
    (hτhit : ∀ V : Set ℂ, IsOpen V →
      AEEventIn P (filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s k ω)))
        {ω | (filledBall (D (h ω)) z₀ (τ ω) ∩ V).Nonempty})
    (hle : filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s k ω)) ≤ mΩ)
    (harcs : ∀ (i : ι) (Γ : Set ℂ), IsClosed Γ → arcs i Γ ⊆ Γ)
    (harcsM : ∀ i, MeasurableSet[@Prod.instMeasurableSpace (Set ℂ) ℂ effrosSigma inferInstance]
      {p : Set ℂ × ℂ | p.2 ∈ arcs i p.1})
    (hCtr : ∃ Ψ : ℝ → Set ℂ × Set ℂ → ℂ,
      (∀ r, @Measurable _ _ (@Prod.instMeasurableSpace _ _ effrosSigma effrosSigma) _ (Ψ r)) ∧
      ∀ (K J : Set ℂ) (r : ℝ), IsClosed K → Bornology.IsBounded K → (interior K).Nonempty →
        JordanMap.IsJordanCurve (frontier K) → J ⊆ frontier K → t39jCtr K J r = Ψ r (K, J))
    (hGood : ∃ A : ℕ → Set (Set ℂ × Set ℂ),
      (∀ q, MeasurableSet[@Prod.instMeasurableSpace _ _ effrosSigma effrosSigma] (A q)) ∧
      ∀ (K J : Set ℂ) (q : ℕ), IsClosed K → Bornology.IsBounded K → (interior K).Nonempty →
        JordanMap.IsJordanCurve (frontier K) → J ⊆ frontier K →
        (t39jGoodAct K J q R ↔ (K, J) ∈ A q)) :
    (∃ g : Ω → ℕ, Measurable[filledBallSigmaAt0 D h z₀
        (fun ω => ENNReal.ofReal (s k ω))] g ∧
      (fun ω => t39j7N D h z₀ I₀ (s k) ω) =ᵐ[P] g) ∧
    (∀ i, ∃ g : Ω → ℂ, Measurable[filledBallSigmaAt0 D h z₀
        (fun ω => ENNReal.ofReal (s k ω))] g ∧
      t39jX D h z₀ R I₀ s (fun k => t39j7N D h z₀ I₀ (s k)) k i =ᵐ[P] g) ∧
    (∀ i, AEEventIn P (filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s k ω)))
      (t39jAct D h z₀ R I₀ s (fun k => t39j7N D h z₀ I₀ (s k)) k i)) := by
  have heq := t39h_fbs0_eq D h z₀ hs
  refine t39k5_fields_of_hitI D h z₀ R I₀ s k hs (fun i U hU => ?_)
    (hgood.mono fun ω hω => ⟨hω.2.2.2, hω.2.2.1,
      t39k5j_mem_interior_filledBall _ z₀ (hω.1.trans_le hω.2.1)⟩) hCtr hGood
  have hτhit' : ∀ V : Set ℂ, IsOpen V →
      AEEventIn P (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (s k ω)))
        {ω | (filledBall (D (h ω)) z₀ (τ ω) ∩ V).Nonempty} := fun V hV => by
    rw [← heq]; exact hτhit V hV
  have H := t39k5_hit_aeEventIn h38 hγ hγ2 hD hh z₀ (s k) τ (arcs i) U
    (hgood.mono fun ω hω => ⟨hω.1, hω.2.1, hω.2.2.1⟩) hτhit' (heq ▸ hle) hU (harcs i)
    (harcsM i)
  rw [heq]
  simpa only [hI₀] using H

end LQGMetric.CONF
