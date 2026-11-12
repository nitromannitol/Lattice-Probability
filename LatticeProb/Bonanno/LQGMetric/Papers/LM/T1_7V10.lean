/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V10 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V6
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7E6

/-!
# LM Lemma 5.4 for a.e. grid shift, per field (packet P-VAR (d), the `(g, θ)` swap)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Lemma 5.4 (l. 992–997): "Under the conditional law given `(h, θ)`, a.s.
the internal metrics `{D(·,·;S) : S ∈ 𝒮^ε_θ}` are conditionally independent." P2-LM17b proved it for
every fixed `θ` and `law(h)`-a.e. `g` (`t17e_lem5_4_grid`). Since `θ` is independent of `(h, D)`,
LM's statement is "for a.e. `(g, θ)`"; here we exchange the quantifiers (Tonelli,
`ae_ae_comm`): for `law(h)`-a.e. `g`, for Lebesgue-a.e. `θ`, the square coordinates are independent
under `κ_g`. The needed joint measurability in `(g, θ)` (`t17v_measurableSet_pi`) comes from the
joint measurability of the coordinates in `(θ, D)` (`t17v_measurable_Y`) and a countable π-system
of boxes. Own standard argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint

variable {α Θ β ι E : Type*} [MeasurableSpace α] [MeasurableSpace Θ] [MeasurableSpace β]
  [Fintype ι] [MeasurableSpace E]

lemma t17v_measurable_kernel_set (κ : Kernel α β) [IsMarkovKernel κ] {T : Set (Θ × β)}
    (hT : MeasurableSet T) : Measurable fun x : α × Θ => κ x.1 {d | (x.2, d) ∈ T} := by
  have hT' : MeasurableSet {p : (α × Θ) × β | (p.1.2, p.2) ∈ T} :=
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd) hT
  have := (κ.comap Prod.fst measurable_fst).measurable_kernel_prodMk_left hT'
  simp only [Kernel.comap_apply] at this
  exact this

/-- the product structure of the coordinates is a measurable condition on `(a, θ)` -/
theorem t17v_measurableSet_pi [MeasurableSpace.CountablyGenerated E] (κ : Kernel α β)
    [IsMarkovKernel κ] {Y : Θ × β → ι → E} (hY : Measurable Y) :
    MeasurableSet {x : α × Θ | (κ x.1).map (fun d => Y (x.2, d)) =
      Measure.pi fun k => (κ x.1).map fun d => Y (x.2, d) k} := by
  set C := t17eFinInter (MeasurableSpace.countableGeneratingSet E)
  have hCm : ∀ s ∈ C, MeasurableSet s := fun s hs => measurableSet_of_mem_t17eFinInter
    (fun u hu => MeasurableSpace.measurableSet_countableGeneratingSet hu) hs
  set Bx : Set (Set (ι → E)) := pi univ '' pi univ (fun _ : ι => C) with hBx
  have hBc : Bx.Countable := (countable_univ_pi fun _ =>
    t17eFinInter_countable MeasurableSpace.countable_countableGeneratingSet).image _
  have hsp : IsCountablySpanning C := ⟨fun _ => univ, fun _ => univ_mem_t17eFinInter _,
    iUnion_const _⟩
  have hgen : (inferInstance : MeasurableSpace (ι → E)) = MeasurableSpace.generateFrom Bx :=
    (generateFrom_eq_pi (C := fun _ : ι => C) (fun _ => generateFrom_t17eFinInter)
      (fun _ => hsp)).symm
  have hpi : IsPiSystem Bx := IsPiSystem.pi fun _ => t17eFinInter_isPiSystem _
  have hYθ : ∀ θ : Θ, Measurable fun d => Y (θ, d) := fun θ =>
    hY.comp (measurable_const.prodMk measurable_id)
  have hiff : ∀ x : α × Θ, ((κ x.1).map (fun d => Y (x.2, d)) =
      Measure.pi fun k => (κ x.1).map fun d => Y (x.2, d) k) ↔
      ∀ B ∈ Bx, (κ x.1).map (fun d => Y (x.2, d)) B =
        (Measure.pi fun k => (κ x.1).map fun d => Y (x.2, d) k) B := by
    intro x
    refine ⟨fun h B _ => by rw [h], fun h => ?_⟩
    have : ∀ k, IsProbabilityMeasure ((κ x.1).map fun d => Y (x.2, d) k) := fun k =>
      (Measure.isProbabilityMeasure_map_iff
        ((measurable_pi_apply k).comp (hYθ x.2)).aemeasurable).2 inferInstance
    have : IsProbabilityMeasure ((κ x.1).map fun d => Y (x.2, d)) :=
      (Measure.isProbabilityMeasure_map_iff (hYθ x.2).aemeasurable).2 inferInstance
    exact ext_of_generate_finite Bx hgen hpi h (by simp [measure_univ])
  have hset : {x : α × Θ | (κ x.1).map (fun d => Y (x.2, d)) =
      Measure.pi fun k => (κ x.1).map fun d => Y (x.2, d) k} =
      ⋂ B ∈ Bx, {x : α × Θ | (κ x.1).map (fun d => Y (x.2, d)) B =
        (Measure.pi fun k => (κ x.1).map fun d => Y (x.2, d) k) B} := by
    ext x; simp only [Set.mem_ofPred_eq, mem_iInter]; exact hiff x
  rw [hset]
  refine MeasurableSet.biInter hBc fun B hB => ?_
  obtain ⟨t, ht, rfl⟩ := hB
  have htm : ∀ k, MeasurableSet (t k) := fun k => hCm _ (ht k (mem_univ k))
  have e1 : (fun x : α × Θ => (κ x.1).map (fun d => Y (x.2, d)) (pi univ t)) =
      fun x => κ x.1 {d | (x.2, d) ∈ Y ⁻¹' pi univ t} := by
    funext x; rw [Measure.map_apply (hYθ x.2) (MeasurableSet.univ_pi htm)]; rfl
  have e2 : (fun x : α × Θ => (Measure.pi fun k => (κ x.1).map fun d => Y (x.2, d) k)
      (pi univ t)) = fun x => ∏ k, κ x.1 {d | (x.2, d) ∈ (fun p => Y p k) ⁻¹' t k} := by
    funext x
    rw [Measure.pi_pi]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Measure.map_apply (show Measurable fun d => Y (x.2, d) k from
      (measurable_pi_apply k).comp (hYθ x.2)) (htm k)]; rfl
  refine measurableSet_eq_fun ?_ ?_
  · rw [e1]; exact t17v_measurable_kernel_set κ (hY (MeasurableSet.univ_pi htm))
  · rw [e2]
    exact Finset.measurable_prod _ fun k _ => t17v_measurable_kernel_set κ
      ((measurable_pi_apply k).comp hY (htm k))

/-- **LM Lemma 5.4, per field, for a.e. grid shift** -/
theorem t17v_lem5_4_ae {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} {D : Ω → ContMetric} (hh : IsWholePlaneGFF h P) (hloc : IsLocalMetric P h D)
    {ε : ℝ} (hε : 0 < ε) (s : Finset (ℤ × ℤ)) :
    ∀ᵐ g ∂P.map h, ∀ᵐ θ ∂(volume : Measure (ℝ × ℝ)),
      (condDistrib D h P g).map (t17Y ε θ s) =
        Measure.pi fun k : s => (condDistrib D h P g).map (t17eEnc (t17Square ε θ k)) := by
  have hm := t17v_measurableSet_pi (Θ := ℝ × ℝ) (condDistrib D h P)
    (Y := fun p : (ℝ × ℝ) × ContMetric => t17Y ε p.1 s p.2) (t17v_measurable_Y ε s)
  exact (Measure.ae_ae_comm (μ := P.map h) (ν := (volume : Measure (ℝ × ℝ)))
    (p := fun g θ => (condDistrib D h P g).map (t17Y ε θ s) =
      Measure.pi fun k : s => (condDistrib D h P g).map (t17eEnc (t17Square ε θ k))) hm).2
    (Filter.Eventually.of_forall fun θ => t17e_lem5_4_grid hh hloc hε θ s)

end LQGMetric.LM
