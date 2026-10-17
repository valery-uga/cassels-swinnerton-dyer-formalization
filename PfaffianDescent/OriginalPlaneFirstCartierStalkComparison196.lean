import PfaffianDescent.OriginalPlaneSectionNativeStalk196

/-! The actual m=0 first-Cartier sequence used by193 is compared with
its actual unit-target sequence, then with the constructed principal stalk
sequence. No normalization, quotient or boundary square is assumed. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Whole actual homogeneous plane sequence and actual curve-unit sequence
are isomorphic. The third component is the independently constructed actual
zero-cokernel Iso, and its actual projection law proves the second square. -/
def originalPlaneZeroRestrictionSequenceIso196
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0) :
    homogeneousRestrictionSequence (grading (equationIdeal p hp))
      (cubicSecondEquationHomogeneous p l hp 1 hl) 0 ≅
      cubicSecondEquation_unitRestrictionSequence p l hp 1 hl := by
  let e₁ : sheafOfModules (grading (equationIdeal p hp)) (0 + 1) ≅
      sheafOfModules (grading (equationIdeal p hp)) 1 := eqToIso (by rw [zero_add])
  let e₂ := (unitIsoZeroTwist (grading (equationIdeal p hp))).symm
  let e₃ := cubicSecondEquation_zeroCokernelIsoCurveUnit p l hp hp0 1 hl
    (nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0)
  refine ShortComplex.isoMk e₁ e₂ e₃ ?_ ?_
  · change (𝟙 _) ≫ mulHomogeneousToUnit (grading (equationIdeal p hp))
        (cubicSecondEquationHomogeneous p l hp 1 hl) =
      mulHomogeneous (grading (equationIdeal p hp))
        (cubicSecondEquationHomogeneous p l hp 1 hl) 0 ≫
          (unitIsoZeroTwist (grading (equationIdeal p hp))).inv
    rw [Category.id_comp]
    rfl
  · exact (cubicSecondEquation_zeroCokernelIsoCurveUnit_π p l hp hp0 1 hl
      (nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0)).symm

/-- The ORIGINAL zero-twist sequence, not a substituted coefficient
sequence, has the constructed principal native-stalk presentation. -/
def originalPlaneZeroRestrictionStalkPrincipalIso196
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (y : scheme (projectiveIntersectionIdeal p l hp hl)) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl y ∈
      quotientCoordinateOpen (equationIdeal p hp) j) :
    (homogeneousRestrictionSequence (grading (equationIdeal p hp))
      (cubicSecondEquationHomogeneous p l hp 1 hl) 0).map
        (schemeModuleStalkModuleFunctor (hypersurface p hp)
          (cubicSecondEquationCurveImmersion p l hp 1 hl y)) ≅
      pointCartierYonedaCoefficientComplex (originalPlaneSectionStalkScalar196 p l hp hl y j hx) :=
  ((schemeModuleStalkModuleFunctor (hypersurface p hp)
    (cubicSecondEquationCurveImmersion p l hp 1 hl y)).mapShortComplex.mapIso
      (originalPlaneZeroRestrictionSequenceIso196 p l hp hp0 hl hl0)) ≪≫
    originalPlaneSectionStalkPrincipalIso196 p l hp hp0 hl hl0 y j hx

/-- The SAME original first-Cartier class becomes the actual principal
local class in its constructed native coordinates. This connects the
sequence used by193 with the original curve-stalk quotient. -/
theorem originalPlaneZeroRestrictionStalk_extClass196
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
    let hS := cubicSecondEquation_homogeneousRestrictionSequence_shortExact p l hp hp0 1 hl
      (nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0) 0
    let e := originalPlaneZeroRestrictionStalkPrincipalIso196 p l hp hp0 hl hl0 y j hx
    ((ShortComplex.ShortExact.extClass.{u} (C := (hypersurface p hp).Modules) hS).mapExactFunctor F).comp (Ext.mk₀ e.hom.τ₁) (add_zero 1) =
      (Ext.mk₀ e.hom.τ₃).comp
        (pointCartierYonedaCoefficientComplex_shortExact _
          (originalPlaneSectionStalkScalar_regular196 p l hp hp0 hl hl0 y j hx)).extClass
        (zero_add 1) := by
  dsimp only
  rw [Ext.mapExactFunctor_extClass]
  exact ShortComplex.ShortExact.extClass_naturality _ _
    (originalPlaneZeroRestrictionStalkPrincipalIso196 p l hp hp0 hl hl0 y j hx).hom

/-- Native-stalk image of every genuine first-Cartier boundary agrees with
the principal local boundary after the constructed endpoint identifications. -/
theorem originalPlaneZeroRestrictionStalk_boundary196
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (y : scheme (projectiveIntersectionIdeal p l hp hl)) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl y ∈
      quotientCoordinateOpen (equationIdeal p hp) j)
    [HasExt.{u} (hypersurface p hp).Modules]
    [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk
      (cubicSecondEquationCurveImmersion p l hp 1 hl y)))]
    (M : (hypersurface p hp).Modules)
    (z : Ext.{u} M (homogeneousRestrictionSequence (grading (equationIdeal p hp))
      (cubicSecondEquationHomogeneous p l hp 1 hl) 0).X₃ 1) :
    let F := schemeModuleStalkModuleFunctor (hypersurface p hp)
      (cubicSecondEquationCurveImmersion p l hp 1 hl y)
    let hS := cubicSecondEquation_homogeneousRestrictionSequence_shortExact p l hp hp0 1 hl
      (nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0) 0
    let e := originalPlaneZeroRestrictionStalkPrincipalIso196 p l hp hp0 hl hl0 y j hx
    ((z.comp (ShortComplex.ShortExact.extClass.{u} (C := (hypersurface p hp).Modules) hS) rfl).mapExactFunctor F).comp (Ext.mk₀ e.hom.τ₁) (add_zero 2) =
      ((z.mapExactFunctor F).comp (Ext.mk₀ e.hom.τ₃) (add_zero 1)).comp
        (pointCartierYonedaCoefficientComplex_shortExact _
          (originalPlaneSectionStalkScalar_regular196 p l hp hp0 hl hl0 y j hx)).extClass rfl := by
  dsimp only
  rw [Ext.mapExactFunctor_comp, Ext.comp_assoc_of_third_deg_zero,
    originalPlaneZeroRestrictionStalk_extClass196,
    ← Ext.comp_assoc_of_second_deg_zero]

end PfaffianDescent.Coray
