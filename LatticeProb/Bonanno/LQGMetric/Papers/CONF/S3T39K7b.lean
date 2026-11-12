/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K7b at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K7
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3Sec3W1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9, packet J6e-2 (part 2): the leaf `CONFW.CONFThm3_9RestAll`

`CONFW.CONFThm3_9RestAll` (S3Sec3W1) from DFGPS Lemma 3.8 and the J6d target
`T39K5FieldsJ3` (S3T39K7, fields 4–6 for J3's arcs) at every admissible parameter, through `confThm3_9RestCL_of_K7`.
-/

noncomputable section

open MeasureTheory Set

namespace LQGMetric
namespace CONF

open Blueprint

/-- **`CONFThm3_9RestAll`** from DFGPS Lemma 3.8 and the J6d target for J3's arcs -/
theorem confThm3_9RestAll_of_K7 (h38 : DFGPSLem3_8)
    (HF : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ),
      IsWeakLQGMetric γ D c → ∀ p : CONFParams, p.Valid → p.δ < 1 / 8 →
        CONFLem3_5At γ D c p → T39K5FieldsJ3 γ D c p) :
    CONFW.CONFThm3_9RestAll := by
  intro γ hγ hγ2 D c hD p hp hδ8 H35 χ _
  exact confThm3_9RestCL_of_K7 h38 hγ hγ2 hD H35 hp.2.2.2.2.2
    (HF γ hγ hγ2 D c hD p hp hδ8 H35) χ

end CONF
end LQGMetric
