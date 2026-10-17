import PfaffianDescent.QuarticTwistedCubicAlgebraicQuadraticPiece
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import AllCharacteristics.ProjectiveBaseChange

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u
variable {K : Type u} [Field K]

local notation "I" => standardTwistedCubicHomogeneousIdeal (K := K)

private theorem standardTwistedCubic_chartZero_base_smooth :
    (chartBaseMap I 0).Smooth := by
  let := (chartBaseMap I 0).toAlgebra
  change Algebra.Smooth K (ChartRing I 0)
  let e : MvPolynomial (Fin 1) K ≃ₐ[K] ChartRing I 0 :=
    { (standardTwistedCubic_chartZero_affineEquiv (K := K)).symm with
      commutes' := standardTwistedCubic_affine_toChartZero_C (K := K) }
  have : Algebra.Smooth K (MvPolynomial (Fin 1) K) :=
    { formallySmooth := inferInstance, finitePresentation := inferInstance }
  exact Algebra.Smooth.of_equiv e

private theorem standardTwistedCubic_chartThree_base_smooth :
    (chartBaseMap I 3).Smooth := by
  let := (chartBaseMap I 3).toAlgebra
  change Algebra.Smooth K (ChartRing I 3)
  let e : MvPolynomial (Fin 1) K ≃ₐ[K] ChartRing I 3 :=
    { (standardTwistedCubic_chartThree_affineEquiv (K := K)).symm with
      commutes' := standardTwistedCubic_affine_toChartThree_C (K := K) }
  have : Algebra.Smooth K (MvPolynomial (Fin 1) K) :=
    { formallySmooth := inferInstance, finitePresentation := inferInstance }
  exact Algebra.Smooth.of_equiv e

/-- The standard projective twisted cubic is smooth over its coefficient
field.  Its two end-coordinate affine charts are affine lines. -/
instance standardTwistedCubic_toBase_smooth : Smooth (toBase I) := by
  have hlocal : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  apply (hlocal.iff_of_openCover (standardTwistedCubicOpenCover (K := K))).mpr
  intro b
  cases b
  · change Smooth (chartι I 0 ≫ toBase I)
    rw [chartι_toBase]
    exact (HasRingHomProperty.Spec_iff (P := @Smooth.{u})).mpr
      (standardTwistedCubic_chartZero_base_smooth (K := K))
  · change Smooth (chartι I 3 ≫ toBase I)
    rw [chartι_toBase]
    exact (HasRingHomProperty.Spec_iff (P := @Smooth.{u})).mpr
      (standardTwistedCubic_chartThree_base_smooth (K := K))

/-- Every ground-coordinate twisted-cubic presentation is smooth over its
coefficient field. -/
theorem GroundTwistedCubicPresentation.toBase_smooth
    {J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hJ : GroundTwistedCubicPresentation J) :
    Smooth (toBase J) := by
  obtain ⟨M, hM⟩ := hJ
  have hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) K).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  have hIJ : (standardTwistedCubicHomogeneousIdeal (K := K)).toIdeal = J.toIdeal.map
      (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) K) hdet).toRingHom := by
    change standardTwistedCubicIdeal K = J.toIdeal.map
      (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) K) hdet).toRingHom
    exact hM.symm
  let e := linearCoordinateChangeSchemeIso
    (M : Matrix (Fin 4) (Fin 4) K) hdet J
      (standardTwistedCubicHomogeneousIdeal (K := K)) hIJ
  have he : e.hom ≫ toBase (standardTwistedCubicHomogeneousIdeal (K := K)) = toBase J :=
    linearCoordinateChangeSchemeIso_hom_toBase
      (M : Matrix (Fin 4) (Fin 4) K) hdet J
        (standardTwistedCubicHomogeneousIdeal (K := K)) hIJ
  rw [← he]
  infer_instance

/-- Smoothness of the standard twisted cubic descends through an
algebraic-closure coordinate standardization.  Thus every geometrically
standard twisted-cubic ideal is already a smooth projective curve over its
ground field; no perfectness assumption is involved in this part of
`lem:twisted-cubic`. -/
theorem geometricallyStandardTwistedCubic_toBase_smooth
    {J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgeo : GeometricallyStandardTwistedCubic J) :
    Smooth (toBase J) := by
  let L := AlgebraicClosure K
  let Jbar : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) L) :=
    HomogeneousIdeal.map
      (ambientCoefficientGradedRingHom (algebraMap K L)) J
  have hJ : J.toIdeal.map (MvPolynomial.map (algebraMap K L)) = Jbar.toIdeal := by
    change J.toIdeal.map (MvPolynomial.map (algebraMap K L)) =
      (HomogeneousIdeal.map
        (ambientCoefficientGradedRingHom (algebraMap K L)) J).toIdeal
    rw [HomogeneousIdeal.toIdeal_map]
    rfl
  obtain ⟨M, hM⟩ := hgeo
  have hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) L).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  have hMJ : (standardTwistedCubicHomogeneousIdeal (K := L)).toIdeal =
      Jbar.toIdeal.map
        (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) L) hdet).toRingHom := by
    change standardTwistedCubicIdeal L = Jbar.toIdeal.map
      (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) L) hdet).toRingHom
    rw [← hJ]
    exact hM.symm
  let e := linearCoordinateChangeSchemeIso
    (M : Matrix (Fin 4) (Fin 4) L) hdet Jbar
      (standardTwistedCubicHomogeneousIdeal (K := L)) hMJ
  have he : e.hom ≫ toBase (standardTwistedCubicHomogeneousIdeal (K := L)) =
      toBase Jbar :=
    linearCoordinateChangeSchemeIso_hom_toBase
      (M : Matrix (Fin 4) (Fin 4) L) hdet Jbar
        (standardTwistedCubicHomogeneousIdeal (K := L)) hMJ
  have hsbar : Smooth (toBase Jbar) := by
    rw [← he]
    infer_instance
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth.{u}) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (isPullback_projectiveCoefficientMap
      (algebraMap K L) J Jbar hJ).flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hsbar
/-- The explicit identification of the standard twisted cubic with `P¹` is
an isomorphism over the coefficient field. -/
theorem standardTwistedCubicToProjectiveLine_toBase :
    standardTwistedCubicToProjectiveLine (K := K) ≫ projectiveLineProjToBase K =
      toBase I := by
  change standardTwistedCubicToProjectiveLine (K := K) ≫
    toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) = toBase I
  apply (standardTwistedCubicOpenCover (K := K)).hom_ext
  intro b
  cases b
  · change chartι I 0 ≫ standardTwistedCubicToProjectiveLine (K := K) ≫
        toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) =
          chartι I 0 ≫ toBase I
    rw [← Category.assoc, standardTwistedCubicChartZero_toProjectiveLine,
      Category.assoc, chartι_toBase, ← Spec.map_comp, chartι_toBase]
    apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    apply RingHom.ext
    intro a
    exact lineChartToStandardTwistedCubicChartZero_base (K := K) a
  · change chartι I 3 ≫ standardTwistedCubicToProjectiveLine (K := K) ≫
        toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) =
          chartι I 3 ≫ toBase I
    rw [← Category.assoc, standardTwistedCubicChartThree_toProjectiveLine,
      Category.assoc, chartι_toBase, ← Spec.map_comp, chartι_toBase]
    apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    apply RingHom.ext
    intro a
    exact lineChartToStandardTwistedCubicChartThree_base (K := K) a

/-- The standard projective-line isomorphism of the twisted cubic respects
its structure map to the coefficient field. -/
theorem standardTwistedCubicProjectiveLineProjIso_hom_toBase :
    (standardTwistedCubicProjectiveLineProjIso (K := K)).hom ≫
      projectiveLineProjToBase K = toBase I := by
  exact standardTwistedCubicToProjectiveLine_toBase (K := K)

/-- The projective-line identification attached to a ground-coordinate
presentation is an isomorphism over the coefficient field. -/
theorem GroundTwistedCubicPresentation.schemeIsoProjectiveLine_hom_toBase
    {J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hJ : GroundTwistedCubicPresentation J) :
    (hJ.schemeIsoProjectiveLine).hom ≫ projectiveLineProjToBase K = toBase J := by
  unfold GroundTwistedCubicPresentation.schemeIsoProjectiveLine
  dsimp only
  change
    ((linearCoordinateChangeSchemeIso _ _ J
        (standardTwistedCubicHomogeneousIdeal (K := K)) _).hom ≫
      (standardTwistedCubicProjectiveLineProjIso (K := K)).hom) ≫
        projectiveLineProjToBase K = toBase J
  rw [Category.assoc, standardTwistedCubicProjectiveLineProjIso_hom_toBase]
  exact linearCoordinateChangeSchemeIso_hom_toBase _ _ _ _ _



/-- The all-field ideal-level form of `lem:twisted-cubic` from a separable
coordinate standardization.  The projective-line identification, smoothness,
and rational section are all over the ground field. -/
theorem twistedCubic_descent_separable_overBase
    {J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgeo : SeparableGeometricallyStandardTwistedCubic J) :
    ∃ e : scheme J ≅ projectiveLineProj K,
      e.hom ≫ projectiveLineProjToBase K = toBase J ∧
        Smooth (toBase J) ∧
          ∃ s : Spec (.of K) ⟶ scheme J, s ≫ toBase J = 𝟙 _ := by
  let hground : GroundTwistedCubicPresentation J :=
    groundTwistedCubicPresentation_of_separableGeometricallyStandardTwistedCubic hgeo
  refine ⟨hground.schemeIsoProjectiveLine,
    hground.schemeIsoProjectiveLine_hom_toBase, hground.toBase_smooth, ?_⟩
  exact separableGeometricallyStandardTwistedCubic_has_rational_section hgeo

/-- The perfect-field ideal-level form of `lem:twisted-cubic`, strengthened
with smoothness and an identification with `P¹` over the base field. -/
theorem twistedCubic_descent_perfect_overBase [PerfectField K]
    {J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hgeo : GeometricallyStandardTwistedCubic J) :
    ∃ e : scheme J ≅ projectiveLineProj K,
      e.hom ≫ projectiveLineProjToBase K = toBase J ∧
        Smooth (toBase J) ∧
          ∃ s : Spec (.of K) ⟶ scheme J, s ≫ toBase J = 𝟙 _ := by
  let hground : GroundTwistedCubicPresentation J :=
    groundTwistedCubicPresentation_of_geometricallyStandardTwistedCubic hgeo
  refine ⟨hground.schemeIsoProjectiveLine,
    hground.schemeIsoProjectiveLine_hom_toBase, hground.toBase_smooth, ?_⟩
  exact geometricallyStandardTwistedCubic_has_rational_section hgeo

end PfaffianDescent.QuarticNet
