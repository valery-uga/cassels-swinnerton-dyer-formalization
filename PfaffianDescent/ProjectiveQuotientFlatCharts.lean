import PfaffianDescent.HomogeneousQuotientMap
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flat projective quotients have flat standard charts

Flatness of the projective quotient over its coefficient ring restricts to
each affine standard chart, giving the ring-theoretic flatness premise for
relative ideal base change.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem flat_quotientCharts_of_flat_toBase
    {R : Type u} [CommRing R]
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal)
    (hflat : Flat (toBase J))
    (j : Fin 4) :
    ((chartQuotientMap I J hIJ j).comp (chartBaseMap I j)).Flat := by
  letI : Flat (toBase J) := hflat
  have hchart : Flat (chartι J j ≫ toBase J) := inferInstance
  rw [chartι_toBase, Flat.SpecMap_iff] at hchart
  rw [chartQuotientMap_chartBaseMap I J hIJ j]
  exact hchart

end PfaffianDescent
