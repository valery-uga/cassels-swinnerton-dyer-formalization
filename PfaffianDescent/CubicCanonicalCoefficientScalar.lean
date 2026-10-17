import PfaffianDescent.ProjectiveBaseConstantFraction
import PfaffianDescent.SchemeModuleGlobalScalarStalk
import PfaffianDescent.FieldPointExtResidueCoefficientScalar
import PfaffianDescent.ClosedFieldPointGroundScalarResidue

/-! # Ground-field scaling in the actual canonical point residue coordinate -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
open scoped nonZeroDivisors
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
local notation "CS" => Proj (grading (equationIdeal p hp))
local notation "Y" => sheafOfModules (grading (equationIdeal p hp)) 1

set_option backward.isDefEq.respectTransparency false in
/-- The actual cubic scalar coefficient morphism, in any free target stalk
coordinate, is multiplication by the germ of the actual base constant. -/
theorem cubicCanonicalScalar_conjugateStalk_eq_base_germ_smul
    (c : K) (x : CS)
    (qN : (schemeModuleStalkModuleFunctor CS x).obj Y ≅
      ModuleCat.of ((CS).presheaf.stalk x) ((CS).presheaf.stalk x)) :
    qN.inv ≫ (schemeModuleStalkModuleFunctor CS x).map
      (mulHomogeneous (grading (equationIdeal p hp)) (cubicScalarHomogeneous K p hp c) 1) ≫
        qN.hom =
      (CS).presheaf.germ ⊤ x trivial (affineFunctionHom (hypersurfaceToBase p hp) c) •
        𝟙 _ := by
  exact schemeModuleStalk_conjugate_eq_germ_smul_of_app Y
    (mulHomogeneous (grading (equationIdeal p hp)) (cubicScalarHomogeneous K p hp c) 1)
    (affineFunctionHom (hypersurfaceToBase p hp) c)
    (fun U y => cubicScalarHomogeneous_app_eq_base_constant_smul p hp c 1 U y) x qN

set_option backward.isDefEq.respectTransparency false in
/-- Ground constants scale the actual field-valued canonical residue coordinate
through the specified field extension. Scalar conjugacy and residue compatibility
are proved internally, rather than supplied as hypotheses. -/
theorem cubicCanonicalPointExtResidueCoordinate_scalar
    {L : Type u} [Field L] [Algebra K L]
    (i : Spec (.of L) ⟶ CS) [IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (x : Spec (.of L)) [HasExt.{u} (CS).Modules]
    [HasExt.{u + 1} (ModuleCat ((CS).presheaf.stalk (i x)))]
    (M : (CS).Modules) (f g : (CS).presheaf.stalk (i x))
    (hf : f ∈ ((CS).presheaf.stalk (i x))⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      (((CS).presheaf.stalk (i x)) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal ((CS).presheaf.stalk (i x)))
    (hgm : g ∈ IsLocalRing.maximalIdeal ((CS).presheaf.stalk (i x)))
    (qM : (schemeModuleStalkModuleFunctor CS (i x)).obj M ≅
      ModuleCat.of ((CS).presheaf.stalk (i x))
        (((CS).presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor CS (i x)).obj Y ≅
      ModuleCat.of ((CS).presheaf.stalk (i x)) ((CS).presheaf.stalk (i x)))
    (c : K) (z : Ext.{u} M Y 2) :
    fieldPointExtTwoResidueCoordinate i x M Y f g hf hg hfm hgm qM qN
        (z.comp (Ext.mk₀ (mulHomogeneous (grading (equationIdeal p hp))
          (cubicScalarHomogeneous K p hp c) 1)) (add_zero 2)) =
      algebraMap K L c *
        fieldPointExtTwoResidueCoordinate i x M Y f g hf hg hfm hgm qM qN z := by
  have h := fieldPointExtTwoResidueCoordinate_postcomp_of_conjugate_eq_smul
    i x M Y f g hf hg hfm hgm qM qN
    (mulHomogeneous (grading (equationIdeal p hp)) (cubicScalarHomogeneous K p hp c) 1)
    ((CS).presheaf.germ ⊤ (i x) trivial (affineFunctionHom (hypersurfaceToBase p hp) c))
    (cubicCanonicalScalar_conjugateStalk_eq_base_germ_smul K p hp c (i x) qN) z
  have hr : closedFieldPointResidueRingEquivAt i x
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ((CS).presheaf.stalk (i x)))
        ((CS).presheaf.germ ⊤ (i x) trivial (affineFunctionHom (hypersurfaceToBase p hp) c))) =
      algebraMap K L c :=
    closedFieldPointResidueRingEquivAt_ground_constant_germ_top
      (hypersurfaceToBase p hp) i hi x c
  exact h.trans (congrArg (fun a : L => a *
    fieldPointExtTwoResidueCoordinate i x M Y f g hf hg hfm hgm qM qN z) hr)

end PfaffianDescent.ProjectiveNegativeTwist
