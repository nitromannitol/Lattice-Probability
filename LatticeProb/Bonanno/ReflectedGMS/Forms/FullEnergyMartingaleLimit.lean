/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FullEnergyMartingaleLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreUniformApproximation
import LatticeProb.Bonanno.ReflectedGMS.Forms.CadlagUniformLimit
import LatticeProb.Bonanno.ReflectedGMS.Forms.MartingaleL2Limit

/-! A law-independent, exactly adapted candidate for the full-energy
martingale part. Its approximants are the centered existing core martingales.
This module establishes the path limit; the martingale property requires the
separate L2 identification. -/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace ReflectedGMS
open ReflectedWalk FullNetworkForm

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

noncomputable def fullEnergyCoreIndex (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (U : hilbertDomain G m) : ℕ → CountableResolventCoreIndex V :=
  Classical.choose (exists_countableResolventCore_geometric_approximation G m hm U)

theorem fullEnergyCoreIndex_bound (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (U : hilbertDomain G m) (n : ℕ) :
    ‖countableResolventCoreVector G m (fullEnergyCoreIndex G m hm U n) - U‖ ≤
      (1 / 2 : ℝ) ^ n :=
  Classical.choose_spec (exists_countableResolventCore_geometric_approximation G m hm U) n

noncomputable def fullEnergyMartingaleApprox
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (U : hilbertDomain G m)
    (n : ℕ) (t : ℝ≥0) (ω : PF.Ω) : ℝ :=
  compactResolventCoreMartingale G m hm PF default (fullEnergyCoreIndex G m hm U (2 * n)) t ω -
    compactResolventCoreMartingale G m hm PF default
      (fullEnergyCoreIndex G m hm U (2 * n)) 0 ω

noncomputable def fullEnergyMartingaleLimit
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (U : hilbertDomain G m)
    (t : ℝ≥0) (ω : PF.Ω) : ℝ :=
  limUnder atTop (fun n ↦ fullEnergyMartingaleApprox G m hm PF default U n t ω)

@[simp] theorem fullEnergyMartingaleLimit_zero
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (U : hilbertDomain G m) (ω : PF.Ω) :
    fullEnergyMartingaleLimit G m hm PF default U 0 ω = 0 := by
  simp only [fullEnergyMartingaleLimit, fullEnergyMartingaleApprox, sub_self]
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).limUnder_eq

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (default : V) (U : hilbertDomain G m)

include h hG hm hmsum

theorem fullEnergyMartingaleApprox_isMartingale (z : V) (n : ℕ) :
    Martingale (fullEnergyMartingaleApprox G m hm PF default U n)
      PF.naturalFiltration.rightCont (PF.P z) := by
  have hM := compactResolventCoreMartingale_isMartingale h hG hm hmsum default
    (fullEnergyCoreIndex G m hm U (2 * n)) z
  exact hM.sub (martingale_const_fun PF.naturalFiltration.rightCont (PF.P z)
    (hM.stronglyMeasurable 0) (hM.integrable 0))

theorem stronglyAdapted_fullEnergyMartingaleLimit :
    StronglyAdapted PF.naturalFiltration.rightCont
      (fullEnergyMartingaleLimit G m hm PF default U) :=
  stronglyAdapted_limUnder_atTop (fun n ↦
    (fullEnergyMartingaleApprox_isMartingale h hG hm hmsum default U default n).stronglyAdapted)

theorem fullEnergyMartingaleApprox_memLp_two
    (ν : Measure PF.Ω) [IsFiniteMeasure ν] (n : ℕ) (t : ℝ≥0) :
    MemLp (fullEnergyMartingaleApprox G m hm PF default U n t) 2 ν :=
  (compactResolventCoreMartingale_memLp_two G m hm PF default
    (fullEnergyCoreIndex G m hm U (2 * n)) ν t).sub
      (compactResolventCoreMartingale_memLp_two G m hm PF default
        (fullEnergyCoreIndex G m hm U (2 * n)) ν 0)

theorem fullEnergyMartingaleLimit_ae_cadlag_and_uniform (z : V) :
    ∀ᵐ ω ∂PF.P z,
      IsCadlag (fun t ↦ fullEnergyMartingaleLimit G m hm PF default U t ω) ∧
        ∀ T : ℕ, TendstoUniformlyOn
          (fun n t ↦ fullEnergyMartingaleApprox G m hm PF default U n t ω)
          (fun t ↦ fullEnergyMartingaleLimit G m hm PF default U t ω)
          atTop (Icc 0 (T : ℝ≥0)) := by
  have hgeom := countableResolventCore_centeredMartingale_successive_uniform
    h hG hm hmsum default z U (fullEnergyCoreIndex G m hm U)
    (fullEnergyCoreIndex_bound G m hm U)
  have hcad : ∀ᵐ ω ∂PF.P z, ∀ n : ℕ,
      IsCadlag (fun t ↦ fullEnergyMartingaleApprox G m hm PF default U n t ω) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [compactResolventCoreMartingale_ae_isCadlag h hG hm hmsum default
      (fullEnergyCoreIndex G m hm U (2 * n)) z] with ω hω
    exact hω.sub IsCadlag.const
  filter_upwards [hgeom, hcad] with ω hω hωcad
  let fseq := fun n t ↦ fullEnergyMartingaleApprox G m hm PF default U n t ω
  have hdiff : ∀ T : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ≥0) (T : ℝ≥0),
      ‖fseq (n + 1) t - fseq n t‖ ≤ (1 / 2 : ℝ) ^ n := by
    intro T
    filter_upwards [hω T] with n hn
    intro t ht
    simpa only [fseq, fullEnergyMartingaleApprox, Real.norm_eq_abs] using hn t ht.2
  obtain ⟨f, hfcad, hf⟩ :=
    exists_cadlag_tendstoUniformlyOn_Icc_nat_of_geometric fseq hωcad hdiff
  have heq : (fun t ↦ fullEnergyMartingaleLimit G m hm PF default U t ω) = f := by
    funext t
    obtain ⟨T, ht⟩ := exists_nat_ge t
    have hlim := (hf T).tendsto_at ⟨zero_le, ht⟩
    exact hlim.limUnder_eq
  rw [heq]
  exact ⟨hfcad, hf⟩

end ReflectedGMS
