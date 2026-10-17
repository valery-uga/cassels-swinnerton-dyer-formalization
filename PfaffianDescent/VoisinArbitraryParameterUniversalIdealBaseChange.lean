import PfaffianDescent.ClosedImmersionIdealBaseChangeOverBaseOpenCover
import PfaffianDescent.VoisinArbitraryParameterLocalSurfaceProjection

/-!
# Universal ideal base change under arbitrary parameter-scheme changes

The canonical ideal of the fixed-cubic universal zero-locus immersion
commutes with every scheme change of equation parameters. The proof uses
the normalized affine parameter-cover comparison on the actual local
surface fibres, then glues along the affine refinement of the arbitrary
source.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

theorem fixedCubicSurfaceEquationZeroLocus_universalIdealBaseChange_anyParameter
    {K : Type u} [Field K]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    {E Y : Scheme.{u}} (k : E ⟶ Spec (.of K))
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (hk : h ≫ projectiveParametersToBase K (Fin 4) 3 = k)
    (hflat : Flat (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h))
    (f : Y ⟶ E) :
    IsIso (@closedImmersionIdealBaseChangeHom _ _ _
      (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) f)
      (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)
      (fixedCubicSurfaceEquationZeroLocusToSurface_isClosedImmersion a ha k h)) := by
  let p := pullback.snd (hypersurfaceToBase a ha) k
  let i := fixedCubicSurfaceEquationZeroLocusToSurface a ha k h
  letI : IsClosedImmersion i :=
    fixedCubicSurfaceEquationZeroLocusToSurface_isClosedImmersion a ha k h
  let 𝒰 := (fixedCubicParameterChangeAffineCover h f).openCover
  exact @isIso_closedImmersionIdealBaseChangeHom_of_baseOpenCover _ _ _ _
    p f i (fixedCubicSurfaceEquationZeroLocusToSurface_isClosedImmersion a ha k h)
    𝒰 (fun j => fixedCubicParameterChangeAffineCover_actualFibreIdealBaseChange
      h f a ha k hk hflat j)

end PfaffianDescent
