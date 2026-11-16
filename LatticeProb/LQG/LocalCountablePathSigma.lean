import LatticeProb.Bonanno.SupercriticalConformalCovariance.TV.LocalCountablePath
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs

/-! # Countable generators of the local field modulo constants -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set TopologicalSpace LQGMetric LQGMetric.Blueprint
open SmallGammaGeodesics SmallGammaGeodesics.CC SupercriticalConformalCovariance.TV

namespace LatticeProb.LQG

/-- The countable local path generates all supported mean-zero field pairings. -/
theorem fieldSigma0On_eq_comap_localCountablePath {Ω : Type} (h : Ω → DistC)
    (O : Opens ℂ) (ρ : TestC) (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O)
    (hρ1 : ∫ z, ρ z = 1) :
    fieldSigma0On h O = MeasurableSpace.comap
      (fun ω => localCountablePath O ρ hρO hρ1 (h ω)) inferInstance := by
  let path : Ω → ℕ → ℝ := fun ω => localCountablePath O ρ hρO hρ1 (h ω)
  let m : MeasurableSpace Ω := MeasurableSpace.comap path inferInstance
  let A : Ω → DistOn O := fun ω => restrictTo O (h ω) - h ω ρ • intDist O
  have hA : Measurable[m] A := by
    let : MeasurableSpace Ω := m
    rw [LQGMetric.distOn_measurableSpace_eq_comap O, measurable_comap_iff]
    apply measurable_pi_iff.mpr
    intro j
    have hm : Measurable[m] (fun ω => path ω (Nat.pair j.1 j.2)) :=
      ((measurable_pi_apply (Nat.pair j.1 j.2)) :
        Measurable (fun f : ℕ → ℝ => f (Nat.pair j.1 j.2))).comp (comap_measurable path)
    convert hm using 1
    funext ω
    change h ω (inclTest O (distGen O j)) - h ω ρ * intDist O (distGen O j) = _
    rw [intDist_apply]
    simp only [path, localCountablePath, localMeanZeroGen, Nat.unpair_pair,
      recTest, map_sub, map_smul, smul_eq_mul, coe_inclTest]
    ring
  apply le_antisymm
  · rw [fieldSigma0On, ← measurable_iff_comap_le]
    apply measurable_pi_iff.mpr
    intro φ
    have hm := (measurable_distOn_apply (testOnOfSupp O φ.1.1 φ.2)).comp hA
    convert hm using 1
    funext ω
    change h ω φ.1.1 = h ω (inclTest O (testOnOfSupp O φ.1.1 φ.2)) -
      h ω ρ * intDist O (testOnOfSupp O φ.1.1 φ.2)
    rw [intDist_apply]
    have heq : inclTest O (testOnOfSupp O φ.1.1 φ.2) = φ.1.1 := by
      ext z
      change (inclTest O (testOnOfSupp O φ.1.1 φ.2) : ℂ → ℝ) z = φ.1.1 z
      rw [coe_inclTest]
      rfl
    rw [heq]
    change h ω φ.1.1 = h ω φ.1.1 - h ω ρ * (∫ z, φ.1.1 z)
    rw [φ.1.2, mul_zero, sub_zero]
  · rw [← measurable_iff_comap_le]
    let : MeasurableSpace Ω := fieldSigma0On h O
    apply measurable_pi_iff.mpr
    intro n
    exact (measurable_pi_apply (localMeanZeroGen O ρ hρO hρ1 n)).comp
      (comap_measurable (fun ω (φ : TestC0On O) => h ω φ.1.1))

end LatticeProb.LQG
