import PfaffianDescent.VoisinRelativeUniversalDivisor

/-!
# Closed immersion of the universal Voisin equation after arbitrary parameter change

The fibre immersion is the pullback of the universal equation's closed
immersion. This argument does not need a normalized parameter chart or an
affine base scheme.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

private theorem closedImmersion_pullbackSnd
    {W X Y : Scheme.{u}} (i : W ⟶ X) (f : Y ⟶ X)
    [IsClosedImmersion i] :
    IsClosedImmersion (pullback.snd i f) := by
  infer_instance

variable {K : Type u} [Field K]
  (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
  {E T : Scheme.{u}} (k : E ⟶ Spec (.of K))
  (h : E ⟶ projectiveParameters K (Fin 4) 3) (s : T ⟶ E)

/-- The actual equation fibre is the categorical pullback of the universal
closed immersion along the fixed-surface fibre projection. -/
theorem isPullback_fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre :
    IsPullback
      (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre a ha k h s)
      (pullback.fst
        (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s)
      (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s)
      (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h) := by
  let p := pullback.snd (hypersurfaceToBase a ha) k
  let i := fixedCubicSurfaceEquationZeroLocusToSurface a ha k h
  let e := pullbackRightPullbackFstIso p s i
  have heq : fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre a ha k h s =
      e.inv ≫ pullback.snd i (pullback.fst p s) := by
    apply pullback.hom_ext
    · exact (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre_fst
        a ha k h s).trans
        (pullbackRightPullbackFstIso_inv_snd_fst p s i).symm
    · exact (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre_snd
        a ha k h s).trans
        (pullbackRightPullbackFstIso_inv_snd_snd p s i).symm
  apply IsPullback.flip
  apply IsPullback.of_iso_pullback
    (show CommSq
      (pullback.fst (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s)
      (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre a ha k h s)
      i (pullback.fst p s) from
        ⟨(fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre_fst
          a ha k h s).symm⟩) e.symm
  · exact pullbackRightPullbackFstIso_inv_fst p s i
  · exact heq.symm

/-- The actual relative universal-equation fibre is closed in the fixed
cubic surface fibre after any parameter-scheme change. -/
theorem fixedCubicSurfaceEquationZeroLocusFibre_isClosedImmersion_general :
    IsClosedImmersion
      (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre a ha k h s) := by
  let p := pullback.snd (hypersurfaceToBase a ha) k
  let i := fixedCubicSurfaceEquationZeroLocusToSurface a ha k h
  let e := pullbackRightPullbackFstIso p s i
  letI : IsClosedImmersion i := by infer_instance
  have heq : fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre a ha k h s =
      e.inv ≫ pullback.snd i (pullback.fst p s) := by
    apply pullback.hom_ext
    · exact (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre_fst
        a ha k h s).trans
        (pullbackRightPullbackFstIso_inv_snd_fst p s i).symm
    · exact (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre_snd
        a ha k h s).trans
        (pullbackRightPullbackFstIso_inv_snd_snd p s i).symm
  rw [heq]
  have hbase : IsClosedImmersion
      (pullback.snd i (pullback.fst p s)) :=
    closedImmersion_pullbackSnd i (pullback.fst p s)
  exact @IsClosedImmersion.comp _ _ _ e.inv
    (pullback.snd i (pullback.fst p s)) (by infer_instance) hbase

end PfaffianDescent
