import PfaffianDescent.ClosedImmersionCohomologyOneLinearEquiv
import PfaffianDescent.AffineOpenCohomology
import PfaffianDescent.SectionRepresenterTop
import PfaffianDescent.SchemeModuleLocallyRankOneTensor
import PfaffianDescent.FiniteSchemeAlgebra

/-! SOURCE ONLY / UNVERIFIED162. Native unit H1 vanishing for an entire
finite scheme and its actual closed pushforward. No reduction, splitting,
acyclicity or cohomology-comparison premise is supplied. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
variable {K : Type u} [Field K]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A finite scheme is noetherian affine. The literal unit module is
locally rank one, hence QC; native affine section-representer vanishing
and the actual top-unit iso give its intrinsic H1 zero. -/
theorem finiteSchemeUnit_cohomology_one_subsingleton
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K)) [IsFinite g]
    [HasExt.{u} Z.Modules] :
    Subsingleton (schemeModuleCohomology Z
      (SheafOfModules.unit Z.ringCatSheaf) 1) := by
  letI : IsAffine Z := isAffine_of_isAffineHom g
  letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  let O : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  have hO : schemeModuleLocallyRankOne O := by
    intro x
    exact ⟨⊤, trivial, ⟨Iso.refl _⟩⟩
  letI : O.IsLocallyFree := schemeModuleLocallyRankOne_isLocallyFree O hO
  letI : O.IsQuasicoherent := inferInstance
  letI : Subsingleton (Ext.{u}
      (show Z.Modules from sectionRepresenter Z.ringCatSheaf (⊤ : Z.Opens)) O 1) :=
    (sectionRepresenter_ext_one_and_two_subsingleton_of_isAffineOpen
      (⊤ : Z.Opens) (isAffineOpen_top Z) O).1
  exact ext_subsingleton_of_iso_left (sectionRepresenterTopIsoUnit Z) 1

/-- The actual closed pushforward of the entire finite unit has ambient
H1 zero. Native162 affine vanishing and native160 comparison derive this;
no ambient acyclicity or injective preservation certificate is assumed. -/
theorem finiteClosedImmersionUnitPushforward_cohomology_one_subsingleton
    {X Z : Scheme.{u}} (pi : X ⟶ Spec (.of K)) (i : Z ⟶ X)
    [IsClosedImmersion i] [IsFinite (i ≫ pi)] [HasExt.{u} X.Modules] :
    Subsingleton (schemeModuleCohomology X
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) 1) := by
  letI : EnoughInjectives Z.Modules := sheafOfModules_enoughInjectives Z.ringCatSheaf
  letI : HasExt.{u} Z.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} Z.Modules
  letI : Subsingleton (schemeModuleCohomology Z
      (SheafOfModules.unit Z.ringCatSheaf) 1) :=
    finiteSchemeUnit_cohomology_one_subsingleton (i ≫ pi)
  exact (closedImmersion_cohomologyOneLinearEquiv pi i
    (SheafOfModules.unit Z.ringCatSheaf)).symm.injective.subsingleton

end PfaffianDescent.Coray
