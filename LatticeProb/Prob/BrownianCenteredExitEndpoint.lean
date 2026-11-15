import LatticeProb.Prob.BrownianExitEndpointTranslation
import LatticeProb.Prob.BrownianBoundedAffineExitEndpoint

/-! # Normalization of Brownian exit endpoint laws -/

set_option autoImplicit false
noncomputable section

open MeasureTheory BouRabeeGwynne Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- The endpoint law for exit from a bounded open set, normalized about an
arbitrary center by a positive radius, is the exit law in the normalized set. -/
theorem brownian_exit_endpoint_law_normalize {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (c z : Euc d) {r : ℝ} (hr : 0 < r) {V : Set (Euc d)}
    (hV : IsOpen V) (hb : Bornology.IsBounded V) :
    ((stoppedBrownianLaw V z μ).map BouRabeeGwynne.CurveSpace.endPoint).map
        (fun x => r⁻¹ • (x - c)) =
      (stoppedBrownianLaw ((fun x : Euc d => c + r • x) ⁻¹' V)
        (r⁻¹ • (z - c)) μ).map BouRabeeGwynne.CurveSpace.endPoint := by
  let R : ℝ≥0 := ⟨r, le_of_lt hr⟩
  let y : Euc d := r⁻¹ • (z - c)
  let W : Set (Euc d) := (fun x : Euc d => c + r • x) ⁻¹' V
  let S : Set (Euc d) := (fun x : Euc d => z + r • x) ⁻¹' V
  have hR : 0 < R⁻¹ := inv_pos.mpr (show 0 < R by exact_mod_cast hr)
  have hW : IsOpen W := hV.preimage (by fun_prop)
  have hsets : (fun x : Euc d => y + x) ⁻¹' W = S := by
    ext x
    change (c + r • (r⁻¹ • (z - c) + x) ∈ V) ↔ (z + r • x ∈ V)
    rw [smul_add, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  have hscale := brownian_exit_endpoint_law_scale_of_bounded hd hμ R⁻¹ hR z hV hb
  have hcoef : ((R⁻¹ : ℝ≥0) : ℝ)⁻¹ = r := by
    change ((↑(R⁻¹) : ℝ)⁻¹) = (R : ℝ)
    rw [NNReal.coe_inv, inv_inv]
  rw [hcoef] at hscale
  have hscale' : (stoppedBrownianLaw V z μ).map BouRabeeGwynne.CurveSpace.endPoint =
      ((stoppedBrownianLaw S 0 μ).map BouRabeeGwynne.CurveSpace.endPoint).map
        (fun x => z + r • x) := by
    exact hscale
  have htrans : ((stoppedBrownianLaw W y μ).map BouRabeeGwynne.CurveSpace.endPoint).map
      (fun x => x - y) = (stoppedBrownianLaw S 0 μ).map BouRabeeGwynne.CurveSpace.endPoint := by
    simpa only [hsets, sub_self] using stoppedBrownianLaw_endPoint_map_sub hW y y μ
  have hf : Measurable (fun x : Euc d => r⁻¹ • (x - c)) := by fun_prop
  have hg : Measurable (fun x : Euc d => z + r • x) := by fun_prop
  have hk : Measurable (fun x : Euc d => y + x) := by fun_prop
  have hs : Measurable (fun x : Euc d => x - y) := by fun_prop
  rw [hscale', Measure.map_map hf hg]
  have hcomp : (fun x : Euc d => r⁻¹ • ((z + r • x) - c)) =
      (fun x => y + x) := by
    funext x
    dsimp only [y]
    rw [show z + r • x - c = (z - c) + r • x by abel,
      smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  rw [show (fun x : Euc d => r⁻¹ • (x - c)) ∘ (fun x => z + r • x) =
      (fun x => y + x) from hcomp, ← htrans, Measure.map_map hk hs]
  have hid : (fun x : Euc d => y + (x - y)) = id := by
    funext x
    simp only [id_eq]
    abel
  rw [show (fun x : Euc d => y + x) ∘ (fun x => x - y) = id from hid, Measure.map_id]

end LatticeProb
end
