import PfaffianDescent.CubicGroundChartJetResidue
import PfaffianDescent.CubicDerivativeCoordinateScaling

/-! Chart normalization retains the full six derivative directions of
the actual ground cubic kernel family. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicGroundChartJetMap_derivativeFamily_spans
    {F E : Type u} [Field F] [Field E] [Algebra F E] {ι : Type*}
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (j : Fin 4)
    (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet E)
    (hu : ∀ i, IsUnit (J i j))
    (hz : ∀ i, aeval (J i) (P.map (algebraMap F E)) = 0)
    (q : ι → homogeneousSubmodule (Fin 4) F 3)
    (hqzero : ∀ k i, aeval (fun r => (J i r).fst) ((q k).1.map (algebraMap F E)) = 0)
    (hspan : Submodule.span E (Set.range (fun k => fun i : Fin 3 =>
      (aeval (J i) ((q k).1.map (algebraMap F E))).snd)) = ⊤) :
    Submodule.span E (Set.range (fun k => fun i : Fin 3 =>
      (cubicGroundChartJetMap P hP j (J i) (hu i) (hz i)
        ((q k).1.eval₂ (chartBaseMap (equationIdeal P hP) j)
          (linearChartCoordinate (equationIdeal P hP) (coordinate (equationIdeal P hP) j)
            (coordinate_mem (equationIdeal P hP) j)))).snd)) = ⊤ := by
  let s : Fin 3 → E := fun i => (J i j).fst⁻¹ ^ 3
  have hs : ∀ i, s i ≠ 0 := by
    intro i
    exact pow_ne_zero 3 (inv_ne_zero
      (TrivSqZeroExt.isUnit_iff_isUnit_fst.mp (hu i)).ne_zero)
  have hscaled := cubicDerivativeCoordinateScale_span_top s hs
    (fun k i => (aeval (J i) ((q k).1.map (algebraMap F E))).snd) hspan
  have heq :
      (fun k => fun i : Fin 3 =>
        (cubicGroundChartJetMap P hP j (J i) (hu i) (hz i)
          ((q k).1.eval₂ (chartBaseMap (equationIdeal P hP) j)
            (linearChartCoordinate (equationIdeal P hP) (coordinate (equationIdeal P hP) j)
              (coordinate_mem (equationIdeal P hP) j)))).snd) =
      (fun k => fun i : Fin 3 =>
        s i • (aeval (J i) ((q k).1.map (algebraMap F E))).snd) := by
    funext k i
    exact cubicGroundChartJetMap_cubic_derivative P hP j (J i) (hu i) (hz i)
      (q k).1 (q k).2 (hqzero k i)
  rw [heq]
  exact hscaled

end PfaffianDescent
