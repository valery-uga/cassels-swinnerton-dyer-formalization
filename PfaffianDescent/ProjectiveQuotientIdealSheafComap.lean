import PfaffianDescent.ProjectiveQuotientBaseChangePullback
import PfaffianDescent.RelativeClosedImmersionIdealBaseChange

/-!
# The ideal sheaf data of a coefficient-changed projective quotient

The global Cartesian square identifies the ideal sheaf data of the
changed quotient immersion with the comap of the original ideal sheaf.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem schemeQuotientMap_coefficientChanged_ker_eq_comap
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) :
    (schemeQuotientMap (coefficientChangedHomogeneousIdeal f I)
      (coefficientChangedHomogeneousIdeal f J)
      (coefficientChangedHomogeneousIdeal_mono f I J hIJ)).ker =
    (schemeQuotientMap I J hIJ).ker.comap
      (projectiveCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
        (coefficientChangedHomogeneousIdeal_toIdeal f I)) := by
  let q := schemeQuotientMap I J hIJ
  let cI := projectiveCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
    (coefficientChangedHomogeneousIdeal_toIdeal f I)
  let q' := schemeQuotientMap (coefficientChangedHomogeneousIdeal f I)
    (coefficientChangedHomogeneousIdeal f J)
    (coefficientChangedHomogeneousIdeal_mono f I J hIJ)
  let H := (isPullback_schemeQuotientMap_coefficientChanged f I J hIJ).flip
  haveI : IsClosedImmersion q := schemeQuotientMap_closedImmersion I J hIJ
  change q'.ker = q.ker.comap cI
  have he : H.isoPullback.hom ≫ pullback.fst cI q = q' :=
    H.isoPullback_hom_fst
  calc
    q'.ker = (H.isoPullback.hom ≫ pullback.fst cI q).ker :=
      congrArg Scheme.Hom.ker he.symm
    _ = (pullback.fst cI q).ker := by
      rw [Scheme.Hom.ker_comp_of_isIso]
    _ = q.ker.comap cI :=
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion q cI

/-- The same ideal-sheaf identity for any explicitly chosen ideals
obtained by coefficient extension. -/
theorem schemeQuotientMap_coefficient_ker_eq_comap
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (I' J' : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hIJ : I.toIdeal ≤ J.toIdeal) (hI'J' : I'.toIdeal ≤ J'.toIdeal)
    (hI : I.toIdeal.map (MvPolynomial.map f) = I'.toIdeal)
    (hJ : J.toIdeal.map (MvPolynomial.map f) = J'.toIdeal) :
    (schemeQuotientMap I' J' hI'J').ker =
      (schemeQuotientMap I J hIJ).ker.comap
        (projectiveCoefficientMap f I I' hI) := by
  let q := schemeQuotientMap I J hIJ
  let q' := schemeQuotientMap I' J' hI'J'
  let cI := projectiveCoefficientMap f I I' hI
  let H := (isPullback_schemeQuotientMap_coefficient_naturality
    f I J I' J' hIJ hI'J' hI hJ).flip
  haveI : IsClosedImmersion q := schemeQuotientMap_closedImmersion I J hIJ
  change q'.ker = q.ker.comap cI
  have he : H.isoPullback.hom ≫ pullback.fst cI q = q' :=
    H.isoPullback_hom_fst
  calc
    q'.ker = (H.isoPullback.hom ≫ pullback.fst cI q).ker :=
      congrArg Scheme.Hom.ker he.symm
    _ = (pullback.fst cI q).ker := by
      rw [Scheme.Hom.ker_comp_of_isIso]
    _ = q.ker.comap cI :=
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion q cI

/-- The actual ideal sheaf data of the changed curve-in-cubic model
is the comap of the original model's ideal sheaf data. -/
theorem homogeneousModelToCubic_baseChange_ker_eq_comap
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hpJ : p ∈ J.toIdeal)
    (hpC : MvPolynomial.map f p ∈ C.toIdeal)
    (hJC : J.toIdeal.map (MvPolynomial.map f) = C.toIdeal) :
    (homogeneousModelToCubic (MvPolynomial.map f p) (hp.map f) C hpC).ker =
      (homogeneousModelToCubic p hp J hpJ).ker.comap
        (projectiveCoefficientMap f (equationIdeal p hp)
          (equationIdeal (MvPolynomial.map f p) (hp.map f))
          (equationIdeal_map f p hp)) := by
  exact schemeQuotientMap_coefficient_ker_eq_comap f
    (equationIdeal p hp) J
    (equationIdeal (MvPolynomial.map f p) (hp.map f)) C
    (by
      apply Ideal.span_le.mpr
      rintro x rfl
      exact hpJ)
    (by
      apply Ideal.span_le.mpr
      rintro x rfl
      exact hpC)
    (equationIdeal_map f p hp) hJC

end PfaffianDescent
