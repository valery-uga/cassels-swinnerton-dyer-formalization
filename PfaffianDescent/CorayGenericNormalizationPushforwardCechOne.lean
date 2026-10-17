import PfaffianDescent.CorayGenericNormalizationPushforwardAffineExt
import PfaffianDescent.SchemeCoverCechExtDegreeOne

/-! Actual Čech computation of ORIGINAL-X Ext¹ into ACTUAL ν_*O_normalization.
The actual all-affine-open cover, its exact augmentation and image, and
its local degree-zero Ext input are derived internally. This does not yet
compare with Ext¹ on the normalization scheme.
STATUS: UNVERIFIED source only. Root owns compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual canonical all-affine-open cover covers X, directly from
the literal supremum identity. No cover certificate is an input. -/
theorem genericNormalization_affineOpenFamily_coversTop (X : Scheme.{u}) :
    (Opens.grothendieckTopology X).CoversTop (fun i : X.affineOpens => i.1) := by
  apply (Opens.coversTop_iff X (fun i : X.affineOpens => i.1)).mpr
  exact iSup_affineOpens_eq_top X

/-- Every actual ORIGINAL-X Ext¹ class into the actual normalization
pushforward is represented by an actual degree-one Hom cocycle on the
canonical affine-open cover. Actual C₀ Ext¹ is discharged by the preceding
affine chart construction; no QC or acyclicity certificate is an input. -/
theorem genericNormalizationPushforwardUnit_affineCech_degreeOneToExt_surjective
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [HasExt.{u} X.Modules] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let U : X.affineOpens → X.Opens := fun i => i.1
    let M := (Scheme.Modules.pushforward (X.fromSpecStalk (genericPoint X)).fromNormalization).obj
      (SheafOfModules.unit (X.fromSpecStalk (genericPoint X)).normalization.ringCatSheaf)
    Function.Surjective (schemeCoverDegreeOneToExtHom U
      (genericNormalization_affineOpenFamily_coversTop X) M) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let U : X.affineOpens → X.Opens := fun i => i.1
  let M := (Scheme.Modules.pushforward (X.fromSpecStalk (genericPoint X)).fromNormalization).obj
    (SheafOfModules.unit (X.fromSpecStalk (genericPoint X)).normalization.ringCatSheaf)
  letI : Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf U).X 0) M 1) :=
    genericNormalizationPushforwardUnit_affineFamily_degreeZeroExt_one_subsingleton U (fun i => i.2)
  exact schemeCoverDegreeOneToExt_surjective U (genericNormalization_affineOpenFamily_coversTop X) M

/-- The actual canonical affine-cover cocycle quotient computes Ext¹ in
ORIGINAL X.Modules into the ACTUAL pushforward structure module. Exactness,
the image sequence, the unit augmentation and all local Ext are internal.
This is an additive equivalence, not a new K-linear dimension formula. -/
def genericNormalizationPushforwardUnit_affineCechQuotientEquivCohomologyOne
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [HasExt.{u} X.Modules] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let U : X.affineOpens → X.Opens := fun i => i.1
    let M := (Scheme.Modules.pushforward (X.fromSpecStalk (genericPoint X)).fromNormalization).obj
      (SheafOfModules.unit (X.fromSpecStalk (genericPoint X)).normalization.ringCatSheaf)
    DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := M) ⧸
        (schemeCoverDegreeOneToExtHom U (genericNormalization_affineOpenFamily_coversTop X) M).ker ≃+
      schemeModuleCohomology X M 1 := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let U : X.affineOpens → X.Opens := fun i => i.1
  let M := (Scheme.Modules.pushforward (X.fromSpecStalk (genericPoint X)).fromNormalization).obj
    (SheafOfModules.unit (X.fromSpecStalk (genericPoint X)).normalization.ringCatSheaf)
  letI : Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf U).X 0) M 1) :=
    genericNormalizationPushforwardUnit_affineFamily_degreeZeroExt_one_subsingleton U (fun i => i.2)
  exact schemeCoverDegreeOneQuotientEquivCohomologyOne U
    (genericNormalization_affineOpenFamily_coversTop X) M

end PfaffianDescent.Coray
