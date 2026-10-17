import PfaffianDescent.CubicGroundChartJetDerivativeSpan
import PfaffianDescent.CubicElevenPointGroundDerivativeSpan

/-! Full native interpolation yields all six actual ground-chart
derivatives of a ground restriction-kernel basis after normalization. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial HomogeneousLocalization Module
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicElevenPoint_groundKernel_normalizedDerivativeFamily_spans
    {F E A : Type u} [Field F] [Field E] [Algebra F E]
    [AddCommGroup A] [Module F A] [FiniteDimensional F A]
    (R : homogeneousSubmodule (Fin 4) F 3 →ₗ[F] A) (hA : finrank F A ≤ 11)
    (y : Fin 11 → Fin 4 → E) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet E)
    (hresidue : ∀ i r, (J i r).fst = y (i.castAdd 8) r)
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction y J))
    (hmem : ∀ q, R q = 0 → cubicElevenPointValueRestriction y
      (voisinDegreeTenSelectedAvoidance_mapCubicSection (L := E) q) = 0)
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (j : Fin 4)
    (hu : ∀ i, IsUnit (J i j))
    (hz : ∀ i, aeval (J i) (P.map (algebraMap F E)) = 0)
    (B : Basis (Fin 9) F R.ker) :
    Submodule.span E (Set.range (fun k : Fin 9 => fun i : Fin 3 =>
      (cubicGroundChartJetMap P hP j (J i) (hu i) (hz i)
        ((B k).1.1.eval₂ (chartBaseMap (equationIdeal P hP) j)
          (linearChartCoordinate (equationIdeal P hP) (coordinate (equationIdeal P hP) j)
            (coordinate_mem (equationIdeal P hP) j)))).snd)) = ⊤ := by
  apply cubicGroundChartJetMap_derivativeFamily_spans P hP j J hu hz
    (fun k => (B k).1)
  · intro k i
    have hy : (fun r => (J i r).fst) = y (i.castAdd 8) := funext (hresidue i)
    rw [hy]
    have h := congrFun (hmem (B k).1 (LinearMap.mem_ker.mp (B k).2)) (i.castAdd 8)
    simp only [cubicElevenPointValueRestriction, homogeneousSectionRestriction_apply,
      finite_product_evaluation_apply, Pi.zero_apply] at h
    exact h
  · exact cubicElevenPoint_groundKernel_derivativeFamily_spans R hA y J
      hresidue hfull hmem B

end PfaffianDescent
