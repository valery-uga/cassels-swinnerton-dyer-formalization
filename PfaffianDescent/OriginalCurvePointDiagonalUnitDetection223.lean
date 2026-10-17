import PfaffianDescent.OriginalCurvePointDiagonalClassNonzero222
import PfaffianDescent.CubicDiagonalUnitDetection223

/-! The original geometry derives actual diagonal-unit nonvanishing from
SAME222/218 witnesses, with no nonzero or comparison certificate. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective PfaffianDescent.ProjectiveNegativeTwist PfaffianDescent.IdealSheafDataModule
open PfaffianDescent.SchemeModuleInternalHom
open scoped nonZeroDivisors
namespace PfaffianDescent.Coray
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

/-- The SAME original whole extension and quotient give a nonzero actual
rational-diagonal unit image.222 internally constructs its supported class;
223 transports literal support/twist maps and221 detects the unit image.
There is no desired class, boundary, trace or nonzero premise. -/
theorem originalCurvePoint_exists_nonzeroDiagonalUnitClass223
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (eX : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    [IsIntegral X] [IsLocallyNoetherian X]
    [HasExt.{u} X.Modules] [HasExt.{u} (hypersurface p hp).Modules]
    (P : closedPoints X) [IsDiscreteValuationRing (X.presheaf.stalk P.1)]
    [HasExt.{u + 1} (ModuleCat.{u} (X.presheaf.stalk P.1))]
    (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl (eX.hom P.1) ∈
      quotientCoordinateOpen (equationIdeal p hp) j) :
    let Y := hypersurface p hp
    let s := eX.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
    let pi := hypersurfaceToBase p hp
    let piX := s ≫ pi
    letI := AllCharacteristics.pointAlgebra piX P.1
    let L := X.residueField P.1
    letI : Module.Finite K L := AllCharacteristics.closedPoint_moduleFinite piX P
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let iY := i ≫ s
    let hi : iY ≫ pi = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
      exact (Category.assoc i s pi).trans (AllCharacteristics.pointAlgebra_spec piX P.1).symm
    let YL := schemeBaseChangeToField (L := L) Y pi
    let q := cubicPointTraceFieldBaseChangeProjection K L pi
    let d := cubicPointTraceFieldBaseChangeTensorDiagonal K L
    let jY := cubicPointTraceFieldBaseChangeTensorPointToAmbient K L pi iY hi
    let xL := jY (d (default : Spec (.of L)))
    let pL := p.map (algebraMap K L)
    let hpL := hp.map (algebraMap K L)
    let iCoeff := cubicDiagonalCoefficientPoint223 K L p hp iY hi
    let R := Y.presheaf.stalk (s P.1)
    let f := originalPlaneSectionStalkScalar196 p l hp hl (eX.hom P.1) j hx
    let S : ShortComplex X.Modules := incrementCokernelSequence (closedImmersionModuleToUnit i)
    ∀ (hExtR : HasExt.{u + 1} (ModuleCat.{u} R))
      (hExtC : HasExt.{u + 1} (ModuleCat.{u} (R ⧸ Ideal.span {f})))
      (hExtYL : HasExt.{u} YL.Modules)
      (hExtRL : HasExt.{u + 1} (ModuleCat.{u} (YL.presheaf.stalk xL)))
      (hExtCoeff : HasExt.{u} (hypersurface pL hpL).Modules)
      (hExtAmbient : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) L)).Modules)
      (hExtLocalAmbient : HasExt.{u + 1} (ModuleCat.{u}
        ((Proj (MvPolynomial.homogeneousSubmodule (Fin 4) L)).presheaf.stalk
          (hypersurfaceAmbientPoint pL hpL (iCoeff default)))))
      (hExtLocalCoeff : HasExt.{u + 1} (ModuleCat.{u}
        ((hypersurface pL hpL).presheaf.stalk (iCoeff default)))),
    letI := hExtR
    letI := hExtC
    letI := hExtYL
    letI := hExtRL
    letI := hExtCoeff
    letI := hExtAmbient
    letI := hExtLocalAmbient
    letI := hExtLocalCoeff
    ∃ (hS : S.ShortExact)
      (E : S.X₃ ≅ (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)),
      let z := originalCurvePointSurfaceFirstCartierClass210 p l hp hp0 hl hl0 X eX i hS E
      let c := closedImmersionIdealTwistSequenceUnitTargetIso iY
      let zPoint := (Ext.mk₀.{u} (C := Y.Modules) c.inv).comp z (zero_add 2)
      let zDiagonal := cubicPointTraceFieldBaseChangeDiagonalExtClass K L pi iY hi _ 2 zPoint
      (Ext.mk₀.{u} (C := YL.Modules) (closedImmersionUnitToPushforwardUnit
        (cubicPointTraceFieldBaseChangeRationalPoint K L pi iY hi))).comp zDiagonal
        (zero_add 2) ≠ 0 := by
  classical
  dsimp only
  intro hExtR hExtC hExtYL hExtRL hExtCoeff hExtAmbient hExtLocalAmbient hExtLocalCoeff
  letI := hExtR
  letI := hExtC
  letI := hExtYL
  letI := hExtRL
  letI := hExtCoeff
  letI := hExtAmbient
  letI := hExtLocalAmbient
  letI := hExtLocalCoeff
  let Y := hypersurface p hp
  let s := eX.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
  let pi := hypersurfaceToBase p hp
  let piX := s ≫ pi
  letI := AllCharacteristics.pointAlgebra piX P.1
  let L := X.residueField P.1
  letI : Module.Finite K L := AllCharacteristics.closedPoint_moduleFinite piX P
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let iY := i ≫ s
  let hi : iY ≫ pi = Spec.map (CommRingCat.ofHom (algebraMap K L)) :=
    (Category.assoc i s pi).trans (AllCharacteristics.pointAlgebra_spec piX P.1).symm
  obtain ⟨hS, E, _, hDiagonal⟩ :=
    originalCurvePoint_exists_nonzeroDiagonalSupportedClass222 p l hp hp0 hl hl0 X eX P j hx
      hExtR hExtC hExtYL hExtRL
  let z := originalCurvePointSurfaceFirstCartierClass210 p l hp hp0 hl hl0 X eX i hS E
  let c := closedImmersionIdealTwistSequenceUnitTargetIso iY
  let zPoint := (Ext.mk₀.{u} (C := Y.Modules) c.inv).comp z (zero_add 2)
  let zDiagonal := cubicPointTraceFieldBaseChangeDiagonalExtClass K L pi iY hi _ 2 zPoint
  exact ⟨hS, E, cubicDiagonalClass_unitPrecomp_ne_zero223 K L p hp hp0 iY hi
    hExtYL hExtCoeff hExtAmbient hExtLocalAmbient hExtLocalCoeff zDiagonal hDiagonal⟩

end PfaffianDescent.Coray
