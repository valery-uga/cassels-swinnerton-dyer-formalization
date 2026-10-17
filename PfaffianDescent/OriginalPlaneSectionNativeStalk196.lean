import PfaffianDescent.NativeRankOneStalkKernel196
import PfaffianDescent.CorayCubicSecondEquationActualCurveUnit
import PfaffianDescent.CorayCubicLinearPairH1RankOne
import PfaffianDescent.SchemeModuleLocalIsoGerm
import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The original unsaturated (p,l) plane section, its literal curve→surface
stalk map, and the first Cartier sequence in actual standard-chart coordinates.
No quotient, equation-regularity or sequence comparison certificate is input. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ORIGINAL plane restriction sequence mapped by the actual native
surface-stalk functor at the image of the ORIGINAL whole section point. -/
def originalPlaneSectionStalkComplex196
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hl : l.IsHomogeneous 1)
    (y : scheme (projectiveIntersectionIdeal p l hp hl)) :
    ShortComplex (ModuleCat ((hypersurface p hp).presheaf.stalk
      (cubicSecondEquationCurveImmersion p l hp 1 hl y))) :=
  (cubicSecondEquation_unitRestrictionSequence p l hp 1 hl).map
    (schemeModuleStalkModuleFunctor (hypersurface p hp)
      (cubicSecondEquationCurveImmersion p l hp 1 hl y))

/-- The negative-one coordinate is constructed from the actual standard
coordinate trivialization on the original surface, not supplied as data. -/
def originalPlaneSectionFirstStalkIso196
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hl : l.IsHomogeneous 1)
    (y : scheme (projectiveIntersectionIdeal p l hp hl)) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl y ∈
      quotientCoordinateOpen (equationIdeal p hp) j) :
    (originalPlaneSectionStalkComplex196 p l hp hl y).X₁ ≅
      ModuleCat.of ((hypersurface p hp).presheaf.stalk
        (cubicSecondEquationCurveImmersion p l hp 1 hl y))
        ((hypersurface p hp).presheaf.stalk
          (cubicSecondEquationCurveImmersion p l hp 1 hl y)) :=
  schemeModuleLocalUnitStalkIso (quotientCoordinateOpen (equationIdeal p hp) j)
    ⟨cubicSecondEquationCurveImmersion p l hp 1 hl y, hx⟩
    (sheafOfModules (grading (equationIdeal p hp)) 1)
    (quotientCoordinateNegativeTwistUnitIso_all (equationIdeal p hp) j 1)

/-- The scalar of the ACTUAL original linear-plane multiplication map in
its actual negative-one/unit chart coordinates. -/
def originalPlaneSectionStalkScalar196
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hl : l.IsHomogeneous 1)
    (y : scheme (projectiveIntersectionIdeal p l hp hl)) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl y ∈
      quotientCoordinateOpen (equationIdeal p hp) j) :
    (hypersurface p hp).presheaf.stalk (cubicSecondEquationCurveImmersion p l hp 1 hl y) :=
  pointCartierNativeStalkScalar (originalPlaneSectionStalkComplex196 p l hp hl y)
    (originalPlaneSectionFirstStalkIso196 p l hp hl y j hx)
    (schemeModuleUnitStalkIso (hypersurface p hp)
      (cubicSecondEquationCurveImmersion p l hp 1 hl y))

/-- Original smoothness and the nonzero linear plane yield genuine local
short exactness; no curve integrality or residue separability is needed. -/
theorem originalPlaneSectionStalkComplex_shortExact196
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (y : scheme (projectiveIntersectionIdeal p l hp hl)) :
    (originalPlaneSectionStalkComplex196 p l hp hl y).ShortExact :=
  (cubicSecondEquation_unitRestrictionSequence_shortExact p l hp hp0 1 hl
    (nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0)).map_of_exact _

theorem originalPlaneSectionStalkScalar_regular196
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (y : scheme (projectiveIntersectionIdeal p l hp hl)) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl y ∈
      quotientCoordinateOpen (equationIdeal p hp) j) :
    originalPlaneSectionStalkScalar196 p l hp hl y j hx ∈
      ((hypersurface p hp).presheaf.stalk
        (cubicSecondEquationCurveImmersion p l hp 1 hl y))⁰ :=
  pointCartierNativeStalkScalar_regular _
    (originalPlaneSectionStalkComplex_shortExact196 p l hp hp0 hl hl0 y)
    (originalPlaneSectionFirstStalkIso196 p l hp hl y j hx)
    (schemeModuleUnitStalkIso (hypersurface p hp)
      (cubicSecondEquationCurveImmersion p l hp 1 hl y))

/-- Kernel of the LITERAL original plane immersion stalk map. Zero
detection is derived from actual closed-immersion stalk naturality. -/
theorem originalPlaneSectionStalkMap_kernel196
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (y : scheme (projectiveIntersectionIdeal p l hp hl)) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl y ∈
      quotientCoordinateOpen (equationIdeal p hp) j) :
    RingHom.ker ((cubicSecondEquationCurveImmersion p l hp 1 hl).stalkMap y).hom =
      Ideal.span ({originalPlaneSectionStalkScalar196 p l hp hl y j hx} : Set _) := by
  let i := cubicSecondEquationCurveImmersion p l hp 1 hl
  let x := i y
  let S := originalPlaneSectionStalkComplex196 p l hp hl y
  let e₁ := originalPlaneSectionFirstStalkIso196 p l hp hl y j hx
  let e₂ := schemeModuleUnitStalkIso (hypersurface p hp) x
  apply nativeRankOneStalkKernel196 S
    (originalPlaneSectionStalkComplex_shortExact196 p l hp hp0 hl hl0 y) e₁ e₂
    (i.stalkMap y).hom
  intro r
  exact closedImmersionUnitToPushforwardUnit_stalkMap_eq_zero_iff
    i i.isClosedEmbedding.isInducing y r

/-- Principal quotient of the ORIGINAL surface stalk is canonically the
ORIGINAL whole-section stalk, through the literal original stalk map. -/
def originalPlaneSectionStalkQuotientEquiv196
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (y : scheme (projectiveIntersectionIdeal p l hp hl)) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl y ∈
      quotientCoordinateOpen (equationIdeal p hp) j) :
    ((hypersurface p hp).presheaf.stalk (cubicSecondEquationCurveImmersion p l hp 1 hl y) ⧸
      Ideal.span ({originalPlaneSectionStalkScalar196 p l hp hl y j hx} : Set _)) ≃+*
      (scheme (projectiveIntersectionIdeal p l hp hl)).presheaf.stalk y :=
  (Ideal.quotEquivOfEq (originalPlaneSectionStalkMap_kernel196 p l hp hp0 hl hl0 y j hx).symm).trans
    (((cubicSecondEquationCurveImmersion p l hp 1 hl).stalkMap y).hom.quotientKerEquivOfSurjective
      ((cubicSecondEquationCurveImmersion p l hp 1 hl).stalkMap_surjective y))

theorem originalPlaneSectionStalkQuotientEquiv_mk196
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (y : scheme (projectiveIntersectionIdeal p l hp hl)) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl y ∈
      quotientCoordinateOpen (equationIdeal p hp) j)
    (r : (hypersurface p hp).presheaf.stalk
      (cubicSecondEquationCurveImmersion p l hp 1 hl y)) :
    originalPlaneSectionStalkQuotientEquiv196 p l hp hp0 hl hl0 y j hx
      (Ideal.Quotient.mk _ r) = (cubicSecondEquationCurveImmersion p l hp 1 hl).stalkMap y r := by
  simp only [originalPlaneSectionStalkQuotientEquiv196, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ r

/-- Whole actual plane-Cartier stalk sequence, including its actual quotient
endpoint and projection, in internally constructed principal coordinates. -/
def originalPlaneSectionStalkPrincipalIso196
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (y : scheme (projectiveIntersectionIdeal p l hp hl)) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl y ∈
      quotientCoordinateOpen (equationIdeal p hp) j) :
    originalPlaneSectionStalkComplex196 p l hp hl y ≅
      pointCartierYonedaCoefficientComplex (originalPlaneSectionStalkScalar196 p l hp hl y j hx) :=
  pointCartierNativeStalkPrincipalIso _
    (originalPlaneSectionStalkComplex_shortExact196 p l hp hp0 hl hl0 y)
    (originalPlaneSectionFirstStalkIso196 p l hp hl y j hx)
    (schemeModuleUnitStalkIso (hypersurface p hp)
      (cubicSecondEquationCurveImmersion p l hp 1 hl y))

/-- The WHOLE principal comparison preserves the actual native quotient
projection and actual unit coordinate, not merely its three endpoints. -/
theorem originalPlaneSectionStalkPrincipalIso_projection196
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (y : scheme (projectiveIntersectionIdeal p l hp hl)) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl y ∈
      quotientCoordinateOpen (equationIdeal p hp) j) :
    (originalPlaneSectionStalkComplex196 p l hp hl y).g ≫
      (originalPlaneSectionStalkPrincipalIso196 p l hp hp0 hl hl0 y j hx).hom.τ₃ =
      (schemeModuleUnitStalkIso (hypersurface p hp)
        (cubicSecondEquationCurveImmersion p l hp 1 hl y)).hom ≫
        (pointCartierYonedaCoefficientComplex
          (originalPlaneSectionStalkScalar196 p l hp hl y j hx)).g :=
  pointCartierNativeStalkQuotientIso_square _
    (originalPlaneSectionStalkComplex_shortExact196 p l hp hp0 hl hl0 y)
    (originalPlaneSectionFirstStalkIso196 p l hp hl y j hx)
    (schemeModuleUnitStalkIso (hypersurface p hp)
      (cubicSecondEquationCurveImmersion p l hp 1 hl y))

/-- Actual global first-Cartier extClass becomes its principal native class.
This is derived from the entire constructed sequence Iso. -/
theorem originalPlaneSectionStalk_extClass196
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (y : scheme (projectiveIntersectionIdeal p l hp hl)) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl y ∈
      quotientCoordinateOpen (equationIdeal p hp) j)
    [HasExt.{u} (hypersurface p hp).Modules]
    [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk
      (cubicSecondEquationCurveImmersion p l hp 1 hl y)))] :
    let F := schemeModuleStalkModuleFunctor (hypersurface p hp)
      (cubicSecondEquationCurveImmersion p l hp 1 hl y)
    let hS := cubicSecondEquation_unitRestrictionSequence_shortExact p l hp hp0 1 hl
      (nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0)
    let e := originalPlaneSectionStalkPrincipalIso196 p l hp hp0 hl hl0 y j hx
    (hS.extClass.mapExactFunctor F).comp (Ext.mk₀ e.hom.τ₁) (add_zero 1) =
      (Ext.mk₀ e.hom.τ₃).comp
        (pointCartierYonedaCoefficientComplex_shortExact _
          (originalPlaneSectionStalkScalar_regular196 p l hp hp0 hl hl0 y j hx)).extClass
        (zero_add 1) := by
  dsimp only
  rw [Ext.mapExactFunctor_extClass]
  exact ShortComplex.ShortExact.extClass_naturality _ _
    (originalPlaneSectionStalkPrincipalIso196 p l hp hp0 hl hl0 y j hx).hom

end PfaffianDescent.Coray
