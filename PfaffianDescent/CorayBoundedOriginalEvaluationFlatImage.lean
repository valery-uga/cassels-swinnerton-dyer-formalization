import PfaffianDescent.CorayBoundedOriginalEvaluationRationalMap
import PfaffianDescent.CorayProjectiveEvaluationCoefficientNaturality
import AllCharacteristics.FlatImage

/-! Source-only / unverified. The SAME original evaluation point is an
affine morphism. The actual image ideal commutes with actual coefficient
base change by the existing affine-flat kernel theorem. No image or rank
certificate is supplied. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped AlgebraicGeometry PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K L B : Type u} [Field K] [CommRing L] [Algebra K L]
  [Field B] [Algebra K B]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
  [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
variable (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
  (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
variable {m : ℕ}
  (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
  (a : Fin m)

/-- An affine field spectrum maps affinely to the original projective
scheme: its composite to Spec K is affine, and the original structure
map is separated. No hypothetical affine-chart image is substituted. -/
theorem cubicThroughPointBasisGenericPoint_isAffineHom :
    IsAffineHom (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a) := by
  letI : IsAffineHom
      (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a ≫
        toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K))) :=
    inferInstance
  exact IsAffineHom.of_comp
    (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a)
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)))

/-- The actual global image ideal base changes to the image ideal of the
actual Cartesian evaluation map over B. Affineness and flatness of the
actual coefficient morphism are derived from its original projective
base-change square. -/
theorem cubicThroughPointBasisGenericPoint_kernel_fieldBaseChange :
    (pullback.snd
      (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a)
      (projectiveEvaluationCoefficientMap (σ := Fin m) (algebraMap K B))).ker =
        (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a).ker.comap
          (projectiveEvaluationCoefficientMap (σ := Fin m) (algebraMap K B)) := by
  let q := cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a
  let g := projectiveEvaluationCoefficientMap (σ := Fin m) (algebraMap K B)
  letI : IsAffineHom q := cubicThroughPointBasisGenericPoint_isAffineHom p hp hp0 n y hpy j b a
  have hPB : IsPullback g
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) B)))
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)))
      (Spec.map (CommRingCat.ofHom (algebraMap K B))) :=
    isPullback_projectiveCoefficientMap (algebraMap K B) ⊥ ⊥
      (by change (⊥ : Ideal (MvPolynomial (Fin m) K)).map
            (MvPolynomial.map (algebraMap K B)) = ⊥
          exact Ideal.map_bot)
  letI : IsAffineHom g :=
    MorphismProperty.of_isPullback (P := @IsAffineHom.{u}) hPB.flip inferInstance
  letI : Flat g :=
    MorphismProperty.of_isPullback (P := @Flat.{u}) hPB.flip inferInstance
  exact AllCharacteristics.kernel_pullback_snd_of_affine_flat q g

end PfaffianDescent.Coray
end
