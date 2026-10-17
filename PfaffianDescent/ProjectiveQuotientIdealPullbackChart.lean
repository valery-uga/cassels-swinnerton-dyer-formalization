import PfaffianDescent.ClosedImmersionIdealPullbackMonoOnOpen
import PfaffianDescent.ProjectiveQuotientIdealSheafComap

/-!
# Transporting chartwise ideal exactness to a global quotient immersion

The quotient immersion restricted to a standard projective chart has
the same ideal sheaf data as the corresponding affine quotient chart.
Consequently, a nonflat coefficient-change monicity result on the
affine chart supplies the monicity needed for the global ideal map.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem chartQuotientMap_ker_eq_globalRestriction
    {R : Type u} [CommRing R]
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : Fin 4) :
    (Spec.map (CommRingCat.ofHom (chartQuotientMap I J hIJ j))).ker =
      (pullback.fst (chartι I j) (schemeQuotientMap I J hIJ)).ker := by
  let H := isPullback_schemeQuotientMap_chart I J hIJ j
  have he : H.isoPullback.hom ≫
      pullback.fst (chartι I j) (schemeQuotientMap I J hIJ) =
    Spec.map (CommRingCat.ofHom (chartQuotientMap I J hIJ j)) :=
    H.isoPullback_hom_fst
  rw [← he, Scheme.Hom.ker_comp_of_isIso]

theorem chartQuotientMap_globalIdealPullback_mono
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : Fin 4)
    (h : Mono ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom
        (chartCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
          (coefficientChangedHomogeneousIdeal_toIdeal f I) j)))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom (chartQuotientMap I J hIJ j)))))) :
    Mono ((Scheme.Modules.pullback
      ((chartι (coefficientChangedHomogeneousIdeal f I) j) ≫
        projectiveCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
          (coefficientChangedHomogeneousIdeal_toIdeal f I))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (schemeQuotientMap I J hIJ))) := by
  let g := Spec.map (CommRingCat.ofHom
    (chartCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
      (coefficientChangedHomogeneousIdeal_toIdeal f I) j))
  let v := chartι I j
  let i := schemeQuotientMap I J hIJ
  haveI : IsClosedImmersion i := schemeQuotientMap_closedImmersion I J hIJ
  have hker := chartQuotientMap_ker_eq_globalRestriction I J hIJ j
  have hlocal : Mono ((Scheme.Modules.pullback g).map
      (IdealSheafDataModule.closedImmersionModuleToUnit (pullback.fst v i))) := by
    change Mono ((Scheme.Modules.pullback g).map
      (IdealSheafDataModule.idealModuleToUnit (pullback.fst v i).ker))
    rw [← hker]
    exact h
  have hmono := closedImmersionIdealPullback_mono_of_targetOpen g v i hlocal
  have hcomp := chartι_projectiveCoefficientMap f I
    (coefficientChangedHomogeneousIdeal f I)
    (coefficientChangedHomogeneousIdeal_toIdeal f I) j
  change (chartι (coefficientChangedHomogeneousIdeal f I) j) ≫
      projectiveCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
        (coefficientChangedHomogeneousIdeal_toIdeal f I) = g ≫ v at hcomp
  rw [hcomp]
  exact hmono

end PfaffianDescent
