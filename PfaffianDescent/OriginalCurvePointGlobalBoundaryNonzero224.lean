import PfaffianDescent.OriginalCurvePointScalarBoundaryDetection224
import PfaffianDescent.OriginalCurvePointDiagonalUnitDetection223

/-! SOURCE ONLY224. The SAME original whole point extension has a nonzero
ACTUAL global connecting map. The original finite-separable diagonal
nonzero geometry is constructed by222/223, not supplied as a certificate. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist IdealSheafDataModule
open SchemeModuleInternalHom
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

/-- A named literal output proposition. The only quantified inputs below
are native Ext dictionaries for the actual named schemes and local rings. -/
def originalCurvePointBoundaryNonzeroData224
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (eX : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    [HasExt.{u} X.Modules] [HasExt.{u} (hypersurface p hp).Modules]
    (P : closedPoints X)
    [HasExt.{u + 1} (ModuleCat.{u} (X.presheaf.stalk P.1))]
    (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl (eX.hom P.1) ∈
      quotientCoordinateOpen (equationIdeal p hp) j) : Prop :=
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
        (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
      (a : L),
      (Ext.mk₀.{u} (C := X.Modules)
        (closedImmersionUnitToPushforwardUnit i ≫
          fieldPointPushforwardScalarEndomorphismAddHom i a ≫ E.inv)).comp
        hS.extClass (zero_add 1) ≠ 0 ∧
      hS.extClass.postcomp
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) (zero_add 1) ≠ 0

/-- Original curve geometry constructs the SAME hS/E and an actual scalar
section with nonzero connecting value, and thus the literal global boundary
AddHom is nonzero. No desired nonzero, unit, trace or comparison premise. -/
theorem originalCurvePoint_exists_globalBoundaryNonzero224
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
    originalCurvePointBoundaryNonzeroData224 p l hp hp0 hl hl0 X eX P j hx := by
  classical
  dsimp only [originalCurvePointBoundaryNonzeroData224]
  intro hExtR hExtC hExtYL hExtRL hExtCoeff hExtAmbient hExtLocalAmbient hExtLocalCoeff
  letI := hExtR
  letI := hExtC
  letI := hExtYL
  letI := hExtRL
  letI := hExtCoeff
  letI := hExtAmbient
  letI := hExtLocalAmbient
  letI := hExtLocalCoeff
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
  obtain ⟨hS, E, hDiagonalUnit⟩ :=
    originalCurvePoint_exists_nonzeroDiagonalUnitClass223 p l hp hp0 hl hl0 X eX P j hx
      hExtR hExtC hExtYL hExtRL hExtCoeff hExtAmbient hExtLocalAmbient hExtLocalCoeff
  obtain ⟨a, ha⟩ := originalCurvePoint_exists_scalarBoundaryNonzero_of_diagonalUnit224
    (L := L) p l hp hp0 hl hl0 X eX i hi hS E hDiagonalUnit
  refine ⟨hS, E, a, ha, ?_⟩
  intro hzero
  have hvalue := DFunLike.congr_fun hzero
    (Ext.mk₀.{u} (C := X.Modules)
      (closedImmersionUnitToPushforwardUnit i ≫
        fieldPointPushforwardScalarEndomorphismAddHom i a ≫ E.inv))
  apply ha
  change (Ext.mk₀.{u} (C := X.Modules)
    (closedImmersionUnitToPushforwardUnit i ≫
      fieldPointPushforwardScalarEndomorphismAddHom i a ≫ E.inv)).comp
      hS.extClass (zero_add 1) = 0 at hvalue
  exact hvalue

end PfaffianDescent.Coray
