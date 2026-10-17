import PfaffianDescent.CubicPointQuadraticRestrictionCoordinate
import PfaffianDescent.CubicPointQuadraticRestrictionPointFiber

/-! # Identification with actual quadratic restriction to the closed point

The target is the stalk of the original point-twisted quotient
`O_Z tensor O(2)`. Its constructed coordinate is bijective, and the scalar
in the actual point Ext pairing equals the coordinate of the original
closed-immersion restriction of the actual positive quadratic section.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
  [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
  (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
  [HasExt.{u} (hypersurface p hp).Modules]
  [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))]

/-- An actual unit trivialization of the positive quadratic twist on the chosen chart. -/
def cubicPointQuadraticRestrictionPositiveTwoLocalIso :
    (SheafOfModules.overFunctor (hypersurface p hp).ringCatSheaf
      (cubicPointQuadraticRestrictionChartOpen K p hp i)).obj
        (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
    SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
      (SheafOfModules.commRingSheafOver (hypersurface p hp).sheaf
        (cubicPointQuadraticRestrictionChartOpen K p hp i))) :=
  overFunctorIsoUnit_of_restrictIsoUnit
    (cubicPointQuadraticRestrictionChartOpen K p hp i)
    (quotientCoordinatePositiveTwistUnitIso_all (equationIdeal p hp)
      (cubicPointQuadraticRestrictionChartIndex K p hp i) 2)

/-- The constructed coordinate of the actual positive quadratic point fiber. -/
def cubicPointQuadraticRestrictionPointResidueIso :
    (schemeModuleStalkModuleFunctor (hypersurface p hp) (i default)).obj
      (closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 2)).X₃ ≅
    ModuleCat.of ((hypersurface p hp).presheaf.stalk (i default))
      (((hypersurface p hp).presheaf.stalk (i default)) ⧸
        IsLocalRing.maximalIdeal ((hypersurface p hp).presheaf.stalk (i default))) :=
  cubicPointQuadraticRestrictionPointFiberResidueIso i default
    (cubicPointQuadraticRestrictionChartOpen K p hp i)
    (cubicPointQuadraticRestrictionChart_mem K p hp i)
    (positiveSheafOfModules (grading (equationIdeal p hp)) 2)
    (cubicPointQuadraticRestrictionPositiveTwoLocalIso K p hp i)
    (cubicPointQuadraticRestrictionStalkIso K p hp hp0 i)

/-- A bijective field-valued coordinate of the actual point fiber. -/
def cubicPointQuadraticRestrictionPointFiberAddEquiv :
    (schemeModuleStalkModuleFunctor (hypersurface p hp) (i default)).obj
      (closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 2)).X₃ ≃+ L :=
  (cubicPointQuadraticRestrictionPointResidueIso K p hp hp0 i).toLinearEquiv.toAddEquiv.trans
    (closedFieldPointResidueRingEquivAt i default).toAddEquiv

/-- Restriction of an actual positive quadratic section by the original
closed-immersion morphism, followed by its germ at the point. -/
def cubicPointQuadraticRestrictionActualSection
    (s : (positiveSheafOfModules (grading (equationIdeal p hp)) 2).sections) :
    (schemeModuleStalkModuleFunctor (hypersurface p hp) (i default)).obj
      (closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 2)).X₃ :=
  (closedImmersionIdealTwistSequence i
    (positiveSheafOfModules (grading (equationIdeal p hp)) 2)).X₃.presheaf.germ
      ⊤ (i default) trivial
      ((cubicPointQuadraticRestrictionToPoint i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 2)).val.app (op ⊤)
        (PresheafOfModules.sections.eval s (op ⊤)))

set_option backward.isDefEq.respectTransparency false in
/-- The actual point-fiber coordinate commutes with the original restriction
on every global section of the positive quadratic twist. -/
theorem cubicPointQuadraticRestrictionPointFiberAddEquiv_actualSection
    (s : (positiveSheafOfModules (grading (equationIdeal p hp)) 2).sections) :
    cubicPointQuadraticRestrictionPointFiberAddEquiv K p hp hp0 i
      (cubicPointQuadraticRestrictionActualSection K p hp i s) =
    closedFieldPointResidueRingEquivAt i default
      (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal ((hypersurface p hp).presheaf.stalk (i default)))
        ((cubicPointQuadraticRestrictionStalkIso K p hp hp0 i).hom
          ((positiveSheafOfModules (grading (equationIdeal p hp)) 2).presheaf.germ
            ⊤ (i default) trivial (PresheafOfModules.sections.eval s (op ⊤))))) := by
  unfold cubicPointQuadraticRestrictionPointFiberAddEquiv
    cubicPointQuadraticRestrictionActualSection
  change closedFieldPointResidueRingEquivAt i default
    ((cubicPointQuadraticRestrictionPointResidueIso K p hp hp0 i).hom _) = _
  rw [← schemeModuleStalkModuleFunctor_map_germ]
  congr 1
  exact cubicPointQuadraticRestrictionPointFiberResidueIso_restriction i default
    (cubicPointQuadraticRestrictionChartOpen K p hp i)
    (cubicPointQuadraticRestrictionChart_mem K p hp i)
    (positiveSheafOfModules (grading (equationIdeal p hp)) 2)
    (cubicPointQuadraticRestrictionPositiveTwoLocalIso K p hp i)
    (cubicPointQuadraticRestrictionStalkIso K p hp hp0 i) _

set_option backward.isDefEq.respectTransparency false in
/-- The scalar in the actual Ext residue identity is exactly restriction of
the actual positive quadratic section to the actual closed-point fiber,
under the internally constructed compatible fiber isomorphism. -/
theorem cubicPointQuadraticRestrictionScalar_eq_actual_restriction
    (q : MvPolynomial.homogeneousSubmodule (Fin 4) K 2) :
    cubicPointCompatibleQuadraticRestrictionScalar K p hp hp0 i q =
    cubicPointQuadraticRestrictionPointFiberAddEquiv K p hp hp0 i
      (cubicPointQuadraticRestrictionActualSection K p hp i
        (positiveGlobalSectionOfHomogeneous (grading (equationIdeal p hp)) 2
          (cubicQuadraticRestriction K p hp q))) := by
  rw [cubicPointQuadraticRestrictionPointFiberAddEquiv_actualSection]
  exact cubicPointQuadraticRestrictionScalar_eq_residue_germ K p hp hp0 i q

end PfaffianDescent.ProjectiveNegativeTwist
