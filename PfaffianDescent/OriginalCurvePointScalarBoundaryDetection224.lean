import PfaffianDescent.ActualFiniteSeparableScalarDetection224
import PfaffianDescent.OriginalCurvePointScalarBoundary221

/-! SOURCE ONLY224. A bounded intermediate caller preserving the SAME
original point extension and SAME whole quotient isomorphism E. Its diagonal
unit input is explicit; the original factory derives it using223. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open SchemeModuleInternalHom IdealSheafDataModule
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

/-- The SAME actual nonzero diagonal unit restriction forces some actual
scalar section of the SAME original whole point quotient to have nonzero
original connecting value. No inference is made from supported Ext alone. -/
theorem originalCurvePoint_exists_scalarBoundaryNonzero_of_diagonalUnit224
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    [HasExt.{u} X.Modules] [HasExt.{u} (hypersurface p hp).Modules]
    {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (hi : (i ≫ (e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl)) ≫
      hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [HasExt.{u} (schemeBaseChangeToField (L := L)
      (hypersurface p hp) (hypersurfaceToBase p hp)).Modules]
    (hS : (incrementCokernelSequence (closedImmersionModuleToUnit i)).ShortExact)
    (E : (incrementCokernelSequence (closedImmersionModuleToUnit i)).X₃ ≅
      (Scheme.Modules.pushforward i).obj
        (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (hDiagonalUnit :
      let s := e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
      let iY := i ≫ s
      let pi := hypersurfaceToBase p hp
      let c := closedImmersionIdealTwistSequenceUnitTargetIso iY
      let z := originalCurvePointSurfaceFirstCartierClass210 p l hp hp0 hl hl0 X e i hS E
      let zPoint := (Ext.mk₀.{u} (C := (hypersurface p hp).Modules) c.inv).comp z (zero_add 2)
      (Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) (hypersurface p hp) pi).Modules)
        (closedImmersionUnitToPushforwardUnit
          (cubicPointTraceFieldBaseChangeRationalPoint K L pi iY hi))).comp
        (cubicPointTraceFieldBaseChangeDiagonalExtClass K L pi iY hi
          (sheafOfModules (grading (equationIdeal p hp)) 1) 2 zPoint) (zero_add 2) ≠ 0) :
    ∃ a : L,
      (Ext.mk₀.{u} (C := X.Modules)
        (closedImmersionUnitToPushforwardUnit i ≫
          fieldPointPushforwardScalarEndomorphismAddHom i a ≫ E.inv)).comp
        hS.extClass (zero_add 1) ≠ 0 := by
  classical
  let s := e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
  let iY := i ≫ s
  let pi := hypersurfaceToBase p hp
  let c := closedImmersionIdealTwistSequenceUnitTargetIso iY
  let N := (sheafOfModules (grading (equationIdeal p hp)) 1)
  let z := originalCurvePointSurfaceFirstCartierClass210 p l hp hp0 hl hl0 X e i hS E
  let zPoint := (Ext.mk₀.{u} (C := (hypersurface p hp).Modules) c.inv).comp z (zero_add 2)
  obtain ⟨a, ha⟩ := actualFiniteSeparableDiagonalUnit_exists_scalarUnitNonzero224
    K L pi iY hi N 2 zPoint hDiagonalUnit
  refine ⟨a, ?_⟩
  intro hBoundary
  apply ha
  have hTarget := actualSupportedPointUnitTarget_scalarPrecomp221 iY N z a
  rw [← hTarget]
  rw [originalCurvePointSurfaceFirstCartier_unitScalar221 p l hp hp0 hl hl0 X e i hS E a,
    hBoundary, Ext.mapExactFunctor_zero, Ext.comp_zero, Ext.zero_comp, Ext.zero_comp]

end PfaffianDescent.Coray
