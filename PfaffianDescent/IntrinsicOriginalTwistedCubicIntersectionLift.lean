import PfaffianDescent.GroundTwistedCubicCubicIntersection
import PfaffianDescent.IntrinsicFullQuadraticSystem
import PfaffianDescent.AmbientBottomProjectiveIso

/-! Source-only, UNVERIFIED.  The same originally supplied subscheme of the
cubic lifts to its actual intersection with its FULL intrinsic quadratic
base.  Containment follows from section kernels; no radical or coordinate
comparison certificate is an input. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def intrinsicOriginalCubicFullBaseIntersectionIdeal
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface F hF) :=
  QuarticNet.groundTwistedCubicCubicIntersectionIdeal
    (intrinsicFullQuadraticBaseIdeal (i ≫ hypersurfaceToAmbient F hF)) F hF

def intrinsicOriginalCubicFullBaseIntersectionToSurface
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface F hF) :
    scheme (intrinsicOriginalCubicFullBaseIntersectionIdeal F hF i) ⟶
      hypersurface F hF :=
  schemeQuotientMap (equationIdeal F hF)
    (intrinsicOriginalCubicFullBaseIntersectionIdeal F hF i)
    (by
      change (equationIdeal F hF).toIdeal ≤
        (intrinsicFullQuadraticBaseIdeal (i ≫ hypersurfaceToAmbient F hF) ⊔
          equationIdeal F hF).toIdeal
      rw [HomogeneousIdeal.toIdeal_sup]
      exact le_sup_right)

def intrinsicOriginalCubicFullBaseIntersectionToBaseCurve
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface F hF) :
    scheme (intrinsicOriginalCubicFullBaseIntersectionIdeal F hF i) ⟶
      scheme (intrinsicFullQuadraticBaseIdeal (i ≫ hypersurfaceToAmbient F hF)) :=
  schemeQuotientMap
    (intrinsicFullQuadraticBaseIdeal (i ≫ hypersurfaceToAmbient F hF))
    (intrinsicOriginalCubicFullBaseIntersectionIdeal F hF i)
    (by
      change (intrinsicFullQuadraticBaseIdeal (i ≫ hypersurfaceToAmbient F hF)).toIdeal ≤
        (intrinsicFullQuadraticBaseIdeal (i ≫ hypersurfaceToAmbient F hF) ⊔
          equationIdeal F hF).toIdeal
      rw [HomogeneousIdeal.toIdeal_sup]
      exact le_sup_left)

instance intrinsicOriginalCubicFullBaseIntersectionToSurface_closedImmersion
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface F hF) :
    IsClosedImmersion (intrinsicOriginalCubicFullBaseIntersectionToSurface F hF i) :=
  schemeQuotientMap_closedImmersion _ _ _

instance intrinsicOriginalCubicFullBaseIntersectionToBaseCurve_closedImmersion
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface F hF) :
    IsClosedImmersion (intrinsicOriginalCubicFullBaseIntersectionToBaseCurve F hF i) :=
  schemeQuotientMap_closedImmersion _ _ _

theorem intrinsicOriginalCubicFullBaseIntersectionToSurface_ambient
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface F hF) :
    intrinsicOriginalCubicFullBaseIntersectionToSurface F hF i ≫
      hypersurfaceToAmbient F hF =
        quotientProjMap (intrinsicOriginalCubicFullBaseIntersectionIdeal F hF i) :=
  schemeQuotientMap_comp_quotientProjMap _ _ _

theorem intrinsicOriginalCubicFullBaseIntersectionToSurface_toBase
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface F hF) :
    intrinsicOriginalCubicFullBaseIntersectionToSurface F hF i ≫
      hypersurfaceToBase F hF =
        toBase (intrinsicOriginalCubicFullBaseIntersectionIdeal F hF i) :=
  schemeQuotientMap_toBase _ _ _

/-- The original Z is a closed subscheme of the actual summed-ideal
intersection.  The two projections are its original cubic embedding and its
kernel-derived full-base embedding, respectively. -/
theorem intrinsicOriginalCubicFullBaseIntersection_original_lift
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface F hF) [IsClosedImmersion i] :
    ∃ (l : Z ⟶ scheme (intrinsicOriginalCubicFullBaseIntersectionIdeal F hF i))
      (lB : Z ⟶ scheme
        (intrinsicFullQuadraticBaseIdeal (i ≫ hypersurfaceToAmbient F hF))),
      IsClosedImmersion l ∧ IsClosedImmersion lB ∧
      l ≫ intrinsicOriginalCubicFullBaseIntersectionToSurface F hF i = i ∧
      l ≫ intrinsicOriginalCubicFullBaseIntersectionToBaseCurve F hF i = lB ∧
      lB ≫ quotientProjMap
        (intrinsicFullQuadraticBaseIdeal (i ≫ hypersurfaceToAmbient F hF)) =
          i ≫ hypersurfaceToAmbient F hF ∧
      l ≫ quotientProjMap (intrinsicOriginalCubicFullBaseIntersectionIdeal F hF i) =
        i ≫ hypersurfaceToAmbient F hF ∧
      l ≫ toBase (intrinsicOriginalCubicFullBaseIntersectionIdeal F hF i) =
        i ≫ hypersurfaceToBase F hF := by
  let a := i ≫ hypersurfaceToAmbient F hF
  let B := intrinsicFullQuadraticBaseIdeal a
  let lB := IsClosedImmersion.lift (quotientProjMap B) a
    (intrinsicFullQuadraticBaseIdeal_ker_le a)
  have hB : lB ≫ quotientProjMap B = a := IsClosedImmersion.lift_fac _ _ _
  letI : IsClosedImmersion (lB ≫ quotientProjMap B) := by
    rw [hB]
    infer_instance
  have hlB : IsClosedImmersion lB := IsClosedImmersion.of_comp lB (quotientProjMap B)
  obtain ⟨l, hlCurve, hlSurface⟩ :=
    (isPullback_projectiveIntersectionAmbient B (equationIdeal F hF)).exists_lift
      lB i hB
  have hc : l ≫ intrinsicOriginalCubicFullBaseIntersectionToSurface F hF i = i :=
    hlSurface
  letI : IsClosedImmersion (l ≫
      intrinsicOriginalCubicFullBaseIntersectionToSurface F hF i) := by
    rw [hc]
    infer_instance
  have hl : IsClosedImmersion l := IsClosedImmersion.of_comp l
    (intrinsicOriginalCubicFullBaseIntersectionToSurface F hF i)
  refine ⟨l, lB, hl, hlB, hc, hlCurve, hB, ?_, ?_⟩
  · simpa only [Category.assoc, intrinsicOriginalCubicFullBaseIntersectionToSurface_ambient]
      using congrArg (fun (t : Z ⟶ hypersurface F hF) => t ≫ hypersurfaceToAmbient F hF) hc
  · simpa only [Category.assoc, intrinsicOriginalCubicFullBaseIntersectionToSurface_toBase]
      using congrArg (fun (t : Z ⟶ hypersurface F hF) => t ≫ hypersurfaceToBase F hF) hc

end PfaffianDescent
