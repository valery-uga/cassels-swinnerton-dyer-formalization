import PfaffianDescent.ProjectiveQuotientGradedNaturality

/-!
# Global naturality of projective quotients under coefficient change

The quotient immersion and coefficient-change morphism commute as
global scheme morphisms. The proof works through their graded maps,
avoiding elaboration of the standard-chart gluing argument.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem schemeQuotientMap_coefficientChanged_comm
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) :
    schemeQuotientMap (coefficientChangedHomogeneousIdeal f I)
        (coefficientChangedHomogeneousIdeal f J)
        (coefficientChangedHomogeneousIdeal_mono f I J hIJ) ≫
      projectiveCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
        (coefficientChangedHomogeneousIdeal_toIdeal f I) =
    projectiveCoefficientMap f J (coefficientChangedHomogeneousIdeal f J)
        (coefficientChangedHomogeneousIdeal_toIdeal f J) ≫
      schemeQuotientMap I J hIJ := by
  let I' := coefficientChangedHomogeneousIdeal f I
  let J' := coefficientChangedHomogeneousIdeal f J
  let hI'J' := coefficientChangedHomogeneousIdeal_mono f I J hIJ
  let q' := gradedQuotientMap I' J' hI'J'
  let cI := gradedCoefficientMap f I I'
    (coefficientChangedHomogeneousIdeal_toIdeal f I)
  let q := gradedQuotientMap I J hIJ
  let cJ := gradedCoefficientMap f J J'
    (coefficientChangedHomogeneousIdeal_toIdeal f J)
  let hq' := gradedSurjective_irrelevant_le q'
    (gradedQuotientMap_surjective I' J' hI'J')
  let hcI := irrelevant_le_map_gradedCoefficientMap f I I'
    (coefficientChangedHomogeneousIdeal_toIdeal f I)
  let hq := gradedSurjective_irrelevant_le q
    (gradedQuotientMap_surjective I J hIJ)
  let hcJ := irrelevant_le_map_gradedCoefficientMap f J J'
    (coefficientChangedHomogeneousIdeal_toIdeal f J)
  have hgraded : q'.comp cI = cJ.comp q :=
    gradedQuotientMap_coefficientChanged_comm f I J hIJ
  change Proj.map q' hq' ≫ Proj.map cI hcI =
    Proj.map cJ hcJ ≫ Proj.map q hq
  calc
    Proj.map q' hq' ≫ Proj.map cI hcI =
        Proj.map (q'.comp cI)
          (HomogeneousIdeal.irrelevant_le_map_comp hcI hq') :=
      (Proj.map_comp cI q' hcI hq').symm
    _ = Proj.map (cJ.comp q)
          (HomogeneousIdeal.irrelevant_le_map_comp hq hcJ) :=
      projMap_congr I J' (q'.comp cI) (cJ.comp q)
        (HomogeneousIdeal.irrelevant_le_map_comp hcI hq')
        (HomogeneousIdeal.irrelevant_le_map_comp hq hcJ) hgraded
    _ = Proj.map cJ hcJ ≫ Proj.map q hq :=
      Proj.map_comp q cJ hq hcJ

end PfaffianDescent
