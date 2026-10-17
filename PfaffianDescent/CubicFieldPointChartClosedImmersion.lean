import PfaffianDescent.CubicFieldPointComponentChart
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveCubicKernelLift
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! A selected chart of an actual closed field point remains a closed
immersion, and its native linear-chart immersion is the same original point. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicFieldPoint_selectedChart_ambient_eq
    {F L : Type u} [Field F] [CommRing L]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3)
    (i : Spec (.of L) ⟶ hypersurface P hP) (j : Fin 4)
    (g : ChartRing (equationIdeal P hP) j →+* L)
    (hgi : Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal P hP) j = i) :
    cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
      (equationIdeal P hP) ⟨coordinate (equationIdeal P hP) j,
        coordinate_mem (equationIdeal P hP) j⟩ g = i := hgi

theorem cubicFieldPoint_selectedChart_isClosedImmersion
    {F L : Type u} [Field F] [CommRing L]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3)
    (i : Spec (.of L) ⟶ hypersurface P hP) [IsClosedImmersion i] (j : Fin 4)
    (g : ChartRing (equationIdeal P hP) j →+* L)
    (hgi : Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal P hP) j = i) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) := by
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom g) ≫
      chartι (equationIdeal P hP) j) := hgi.symm ▸ inferInstance
  exact IsClosedImmersion.of_comp (Spec.map (CommRingCat.ofHom g))
    (chartι (equationIdeal P hP) j)

theorem cubicFieldPoint_selectedChart_ambient_isClosedImmersion
    {F L : Type u} [Field F] [CommRing L]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3)
    (i : Spec (.of L) ⟶ hypersurface P hP) [IsClosedImmersion i] (j : Fin 4)
    (g : ChartRing (equationIdeal P hP) j →+* L)
    (hgi : Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal P hP) j = i) :
    IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
      (equationIdeal P hP) ⟨coordinate (equationIdeal P hP) j,
        coordinate_mem (equationIdeal P hP) j⟩ g) :=
  (cubicFieldPoint_selectedChart_ambient_eq P hP i j g hgi).symm ▸ inferInstance

end PfaffianDescent
