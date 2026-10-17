import PfaffianDescent.ActualGlobalPositiveTwistConormalDifferentialMap
import PfaffianDescent.ActualPointTwistUntwistRatio

/- SOURCE ONLY / UNVERIFIED. Contracting the actual positive twist at
an actual field point commutes with the GENUINE GLOBAL conormal D map.
The square follows from genuine tensor/unit naturality, not an assumed Phi
comparison. A chosen unit Iso here is auxiliary structural data only. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

lemma actualPointTwistUntwistIso_naturality
    {L : Type u} [Field L] {M N T : (Spec (.of L)).Modules}
    (e : T ≅ SheafOfModules.unit (Spec (.of L)).ringCatSheaf) (d : M ⟶ N) :
    schemeModuleTensorMap d (𝟙 T) ≫ (actualPointTwistUntwistIso N T e).hom =
      (actualPointTwistUntwistIso M T e).hom ≫ d := by
  change (schemeModuleTensorRight T).map d ≫
      (schemeModuleTensorRightIsoUnit e).hom.app N =
    (schemeModuleTensorRightIsoUnit e).hom.app M ≫ (𝟭 _).map d
  exact (schemeModuleTensorRightIsoUnit e).hom.naturality d

lemma actualGlobalPositiveTwistConormalDifferentialMap_contract
    {K L : Type u} [Field K] [Field L]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (q : Spec (.of L) ⟶ scheme I) [IsClosedImmersion q] (m : ℕ)
    (e : (Scheme.Modules.pullback q).obj (positiveSheafOfModules (grading I) m) ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf) :
    actualGlobalPositiveTwistConormalDifferentialMap I q m ≫
      (actualPositiveTwistPullbackTensorIso I q (schemeRelativeDifferentials (toBase I)) m).hom ≫
      (actualPointTwistUntwistIso
        ((Scheme.Modules.pullback q).obj (schemeRelativeDifferentials (toBase I)))
        ((Scheme.Modules.pullback q).obj (positiveSheafOfModules (grading I) m)) e).hom =
    (actualPositiveTwistPullbackTensorIso I q (closedImmersionModule q) m).hom ≫
      (actualPointTwistUntwistIso
        ((Scheme.Modules.pullback q).obj (closedImmersionModule q))
        ((Scheme.Modules.pullback q).obj (positiveSheafOfModules (grading I) m)) e).hom ≫
      actualGlobalClosedConormalDifferentialMap (toBase I) q := by
  unfold actualGlobalPositiveTwistConormalDifferentialMap
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [actualPointTwistUntwistIso_naturality]

end PfaffianDescent
