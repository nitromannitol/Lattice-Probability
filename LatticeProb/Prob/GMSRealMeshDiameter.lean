import LatticeProb.Prob.IndexedCellRealMeshDiameter
import LatticeProb.Bonanno.ReflectedGMS.GMS.ValidCodeSet
import LatticeProb.Bonanno.ReflectedGMS.Environment.GeneralLawTransfer
import LatticeProb.Bonanno.ReflectedGMS.Spatial.GeneralGraphLocalFiniteness

/-! # Diameter decay for cell configuration laws -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open ReflectedGMS ReflectedGMS.GMS ReflectedGMS.Code

namespace LatticeProb.GMSRealMeshDiameter

/-- Under the GMS mass transport and finite expectation hypotheses, the diameters
of every cell containing a point in a fixed scaled ball decay uniformly over
all sufficiently small positive real scales. -/
theorem ae_scaled_cell_diam_lt {μ : Measure GMSSpace} [IsProbabilityMeasure μ]
    (hL : ConnectedAlongLines μ) (hMT : MassTransport μ) (hFE : FiniteExpectation μ) :
    ∀ᵐ H ∂μ, ∀ R : ℝ, ∀ η > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ∀ z ∈ closedBall (0 : Plane) R, ∀ (K : Cell), K ∈ H.1.cells →
        ε⁻¹ • z ∈ (K : Set Plane) → ε * Metric.diam (K : Set Plane) < η := by
  let P := μ.map codeMap
  have hP : GeneralLaws.SupportedOnValidGeneral P := supportedOnValidGeneral_codeMap hL
  have hm : GeneralLaws.MassTransport (GeneralLaws.generalLaw P hP) :=
    massTransport_generalLaw_gms hL hP hMT
  have hf : GeneralLaws.FiniteEnergyMoment (GeneralLaws.generalLaw P hP) :=
    finiteEnergyMoment_generalLaw_gms hL hP hFE
  have hfin := GeneralLaws.ae_finiteRows (GeneralLaws.generalLaw P hP) hm hf
  have hV := GeneralLaws.supportedOnValid_of_generalLaw P hP hfin
  have hmt := GeneralLaws.ambientMassTransport_of_generalLaw P hP hfin hV hm
  have hfe := GeneralLaws.finiteEnergyMoment_validLaw_of_generalLaw P hP hfin hV hf
  have hsub := ReflectedGMS.Spatial.ae_maxDiamHittingBall_finite_and_sublinear
    (EnvironmentLaws.validLaw P hV) hmt hfe.ne
  have hback := ae_of_ae_validLaw_gms hV hsub
  filter_upwards [hback] with H ⟨hv, he⟩
  intro R
  have hd := IndexedCellRealMeshDiameter.scaled_diam_lt_of_maxDiamHittingBall_sublinear
    (decode ⟨H.1.code, hv⟩) he.2.1 R
  intro η hη
  obtain ⟨ε₀, hε₀, hb⟩ := hd η hη
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεsmall z hz K hK hzK
  let v := (CellConfig.cellEquiv H.2).symm ⟨K, hK⟩
  have hvK : (decode ⟨H.1.code, hv⟩).cell v = K :=
    CellConfig.cell_cellEquiv_symm H.2 ⟨K, hK⟩
  have h := hb ε hε hεsmall z hz v (by simpa only [hvK] using hzK)
  simpa only [hvK] using h

end LatticeProb.GMSRealMeshDiameter
