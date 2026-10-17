import PfaffianDescent.CubicCanonicalPointFieldTraceEvaluation
import PfaffianDescent.CubicCanonicalPointResiduePresentation
import PfaffianDescent.FieldPointExtTargetNaturality
import PfaffianDescent.SchemeModuleLocalIsoGerm

/-! # Actual quadratic point residue in compatible coefficient coordinates

The source presentation and regular parameters are those of the constructed
canonical point coordinate. The negative-three target coordinate is constructed
from a projective coordinate chart. Neither invertibility of this raw residue
coordinate nor nonvanishing of the geometric trace coefficient is asserted.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- A free stalk coordinate constructed internally from the standard projective
coordinate cover, for any negative twist. -/
def cubicPointCompatibleNegativeTwistStalkIso
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) (m : ℕ) :
    (schemeModuleStalkModuleFunctor (hypersurface p hp) (i default)).obj
      (sheafOfModules (grading (equationIdeal p hp)) m) ≅
    ModuleCat.of ((hypersurface p hp).presheaf.stalk (i default))
      ((hypersurface p hp).presheaf.stalk (i default)) := by
  let I := equationIdeal p hp
  have hcover : ∃ j : Fin 4, i default ∈ quotientCoordinateOpen I j := by
    have hx : i default ∈ (⨆ j : Fin 4, quotientCoordinateOpen I j) := by
      rw [quotientCoordinateOpen_iSup I]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  let j := Classical.choose hcover
  exact schemeModuleLocalUnitStalkIso (quotientCoordinateOpen I j)
    ⟨i default, Classical.choose_spec hcover⟩
    (sheafOfModules (grading I) m) (quotientCoordinateNegativeTwistUnitIso_all I j m)

variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [hClosed : IsClosedImmersion i]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))]

/-- The actual residue presentation retained from the canonical target. -/
def cubicPointCompatibleResiduePresentation :=
  Classical.choice (cubicCanonicalPointExtTwoCoordinate_residuePresentation K p hp hp0 i)

/-- The raw negative-three point residue, using the same source presentation
and regular parameters as the actual canonical-target coordinate. -/
def cubicPointCompatibleNegativeThreeResidue
    (z : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 3) 2) : L :=
  let d := cubicPointCompatibleResiduePresentation K p hp hp0 i
  fieldPointExtTwoResidueCoordinate i default _ _ d.f d.g d.hf d.hg d.hfm d.hgm
    d.qM (cubicPointCompatibleNegativeTwistStalkIso K p hp i 3) z

/-- Restriction of the actual quadratic multiplication map, evaluated at one
in the internally constructed coefficient stalk coordinates. -/
def cubicPointCompatibleQuadraticRestrictionScalar
    (q : MvPolynomial.homogeneousSubmodule (Fin 4) K 2) : L :=
  let d := cubicPointCompatibleResiduePresentation K p hp hp0 i
  closedFieldPointResidueRingEquivAt i default
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ((hypersurface p hp).presheaf.stalk (i default)))
      (((cubicPointCompatibleNegativeTwistStalkIso K p hp i 3).inv ≫
        (schemeModuleStalkModuleFunctor (hypersurface p hp) (i default)).map
          (mulHomogeneous (grading (equationIdeal p hp))
            (cubicQuadraticRestriction K p hp q) 1) ≫ d.qN.hom) 1))

set_option backward.isDefEq.respectTransparency false in
/-- Actual coefficient multiplication factors through the raw negative-three
residue and the actual conjugated stalk scalar for every point Ext class. -/
theorem cubicPointCompatible_multiplied_coordinate
    (z : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 3) 2)
    (q : MvPolynomial.homogeneousSubmodule (Fin 4) K 2) :
    cubicCanonicalPointExtTwoCoordinate K p hp hp0 i
      (z.comp (Ext.mk₀.{u} (C := (hypersurface p hp).Modules)
        (mulHomogeneous (grading (equationIdeal p hp))
          (cubicQuadraticRestriction K p hp q) 1)) (add_zero 2)) =
    cubicPointCompatibleNegativeThreeResidue K p hp hp0 i z *
      cubicPointCompatibleQuadraticRestrictionScalar K p hp hp0 i q := by
  let d := cubicPointCompatibleResiduePresentation K p hp hp0 i
  rw [d.coordinate_eq]
  exact (fieldPointExtTwoResidueCoordinate_postcomp_two_targets_actual_scalar
    i default _ _ _ d.f d.g d.hf d.hg d.hfm d.hgm d.qM
    (cubicPointCompatibleNegativeTwistStalkIso K p hp i 3) d.qN
    (mulHomogeneous (grading (equationIdeal p hp)) (cubicQuadraticRestriction K p hp q) 1)
    z).trans (mul_comm _ _)

set_option backward.isDefEq.respectTransparency false in
/-- Every actual quadratic point pairing is the field trace of the geometric
coefficient times the raw negative-three residue times the actual restriction
scalar. No chart, scalar compatibility, or trace identity is supplied. -/
theorem cubicPointCompatible_pairing_eq_fieldTrace
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ Proj (grading (equationIdeal p hp))) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((Proj (grading (equationIdeal p hp))).presheaf.stalk (i default)))]
    (z : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (Proj (grading (equationIdeal p hp))).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 3) 2)
    (q : MvPolynomial.homogeneousSubmodule (Fin 4) K 2) :
    cubicIntrinsicNegativeThreeCohomologyTwoEquivDualQuadratic K p hp hp0
      ((Ext.mk₀.{u} (C := (Proj (grading (equationIdeal p hp))).Modules)
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
          (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp z (zero_add 2)) q =
    Algebra.trace K L (cubicCanonicalPointResidueTraceCoefficient K p hp hp0 i hi *
      @cubicPointCompatibleNegativeThreeResidue K _ p hp hp0 hSmooth L _ i hClosed hExt hExtStalk z *
      @cubicPointCompatibleQuadraticRestrictionScalar K _ p hp hp0 hSmooth L _ i hClosed hExt hExtStalk q) := by
  have hpair := @cubicCanonicalPoint_pairing_eq_fieldTrace_multiplied_coordinate
    K _ p hp hp0 hDomain hSmooth L _ _ _ _ i hClosed hi hExtAmbient hExt hExtStalk z q
  rw [@cubicPointCompatible_multiplied_coordinate K _ p hp hp0 hSmooth L _ i hClosed
    hExt hExtStalk z q] at hpair
  simpa only [mul_assoc] using hpair

end PfaffianDescent.ProjectiveNegativeTwist
