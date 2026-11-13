/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.CompactVertexDynkin at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.CompactProcessFiltration
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexDynkinMartingale
import LatticeProb.Bonanno.ReflectedGMS.Forms.RightContinuousMartingaleTransfer

/-! The ordinary Dynkin martingale on the compact realization. The discount-one
potential is an existing continuous coordinate; its occupation compensator has
continuous paths. Finite-horizon bounds permit the checked filtration transfer. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ReflectedGMS
open ReflectedWalk FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

theorem ResolventCompactSpace.potentialCoordinate_norm_le_one
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (y : V) (p : ResolventCompactSpace.Space G m hm) :
    ‖ResolventCompactSpace.potentialCoordinate G m hm y p‖ ≤ 1 := by
  have hp := abs_le.mpr (p.1.2 (Finsupp.single y (1 : ℚ))).property
  change |(p.1.2 (Finsupp.single y (1 : ℚ)) : ℝ)| ≤
    ResolventCompactSpace.bound (Finsupp.single y 1) at hp
  simpa [Real.norm_eq_abs, ResolventCompactSpace.potentialCoordinate,
    ResolventCompactSpace.coordinate, CompactVertexSpace.coordinate,
    ResolventCompactSpace.bound, countableResolventCoreBound] using hp

noncomputable def compactVertexDynkinMartingale (G : ConductanceGraph V)
    (m : V → ℝ) (hm : ∀ v, 0 < m v) (PF : ProcessFamily V)
    (default y : V) (t : ℝ≥0) (ω : PF.Ω) : ℝ :=
  ResolventCompactSpace.potentialCoordinate G m hm y
      (reflectedCompactProcess G m hm PF default t ω) -
    boundedStateOccupationVersion PF (vertexDynkinIntegrand G m 1 y) t ω

theorem stronglyAdapted_compactVertexDynkinMartingale
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default y : V) :
    StronglyAdapted PF.naturalFiltration.rightCont
      (compactVertexDynkinMartingale G m hm PF default y) := by
  intro t
  exact ((ResolventCompactSpace.potentialCoordinate G m hm y).continuous.comp_stronglyMeasurable
    (stronglyAdapted_reflectedCompactProcess_rightCont G m hm PF default t)).sub
      ((stronglyMeasurable_boundedStateOccupationVersion PF
        (vertexDynkinIntegrand G m 1 y) t).mono (PF.naturalFiltration.le_rightCont t))

theorem norm_compactVertexDynkinMartingale_le
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default y : V) (t : ℝ≥0) (ω : PF.Ω) :
    ‖compactVertexDynkinMartingale G m hm PF default y t ω‖ ≤ 1 + 2 * (t : ℝ) := by
  exact (norm_sub_le _ _).trans (by
    have hp := ResolventCompactSpace.potentialCoordinate_norm_le_one G m hm y
      (reflectedCompactProcess G m hm PF default t ω)
    have hA := norm_boundedStateOccupationVersion_le PF
      (vertexDynkinIntegrand G m 1 y) t
      (vertexDynkinIntegrand_bound G m hm (by norm_num : (0 : ℝ) < 1) y) ω
    linarith)

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (default y z : V)

include h hG hmsum

theorem compactVertexDynkinMartingale_ae_eq (t : ℝ≥0) :
    compactVertexDynkinMartingale G m hm PF default y t =ᵐ[PF.P z]
      vertexDynkinMartingale PF G m 1 y t := by
  filter_upwards [reflectedCompactProcess_ae_eq_sample_at_time
    h hG hm hmsum default z t, (h z).2.1 t] with ω hc hx
  obtain ⟨x, hx⟩ := hx.1
  simp only [compactVertexDynkinMartingale, vertexDynkinMartingale, hc,
    reflectedCompactSample, hx, Option.getD_some, Option.elim_some,
    ResolventCompactSpace.potentialCoordinate_vertex]

theorem compactVertexDynkinMartingale_ae_isCadlag :
    ∀ᵐ ω ∂PF.P z,
      IsCadlag (fun t => compactVertexDynkinMartingale G m hm PF default y t ω) := by
  have hb : ∀ q, |vertexDynkinIntegrand G m 1 y q| ≤ 2 := by
    simpa only [← Real.norm_eq_abs] using
      vertexDynkinIntegrand_bound G m hm (by norm_num : (0 : ℝ) < 1) y
  filter_upwards [reflectedCompactProcess_ae_cadlag_and_projection
    h hG hm hmsum default z,
    boundedStateOccupationVersion_ae_eq_all_and_continuous h
      (vertexDynkinIntegrand G m 1 y) hb z] with ω hc hA
  exact (hc.1.continuous_comp
    (ResolventCompactSpace.potentialCoordinate G m hm y).continuous).sub hA.2.isCadlag

theorem compactVertexDynkinMartingale_isMartingale :
    Martingale (compactVertexDynkinMartingale G m hm PF default y)
      PF.naturalFiltration.rightCont (PF.P z) := by
  apply martingale_rightCont_of_ae_eq_of_ae_rightContinuous_of_locallyBounded
    (vertexDynkinMartingale_isMartingale h hG hm hmsum
      (by norm_num : (0 : ℝ) < 1) y z)
    (stronglyAdapted_compactVertexDynkinMartingale G m hm PF default y)
    (compactVertexDynkinMartingale_ae_eq h hG hm hmsum default y z)
    ((compactVertexDynkinMartingale_ae_isCadlag h hG hm hmsum default y z).mono
      fun _ hω => hω.isRightContinuous) (fun T => 1 + 2 * (T : ℝ))
  intro T
  filter_upwards [] with ω
  intro t ht
  exact (norm_compactVertexDynkinMartingale_le G m hm PF default y t ω).trans
    (by have ht' : (t : ℝ) ≤ T := ht; linarith)

end ReflectedGMS
