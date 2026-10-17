import PfaffianDescent.VoisinGaloisBaseChange
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSupportTensorDegree

/-! # The actual retained support is the whole native coefficient tensor spectrum -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def serreIncidenceSupportPullbackIso
    {K L F : Type u} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (i : Spec (.of L) ⟶ X)
    (hi : i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    Spec (.of (L ⊗[K] F)) ≅
      pullback (pullback.fst base (Spec.map (CommRingCat.ofHom (algebraMap K F)))) i :=
  (pullbackSpecIso K L F).symm ≪≫
    (finitePointBaseChangeToAmbient_isPullback (L := F) base i hi).isoPullback

@[reassoc]
theorem serreIncidenceSupportPullbackIso_toField
    {K L F : Type u} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (i : Spec (.of L) ⟶ X)
    (hi : i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    (serreIncidenceSupportPullbackIso base i hi).hom ≫
      pullback.fst (pullback.fst base (Spec.map (CommRingCat.ofHom (algebraMap K F)))) i ≫
      pullback.snd base (Spec.map (CommRingCat.ofHom (algebraMap K F))) =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := F)).toRingHom) := by
  simp only [serreIncidenceSupportPullbackIso, Iso.trans_hom, Category.assoc,
    IsPullback.isoPullback_hom_fst_assoc, finitePointBaseChangeToAmbient_snd]
  exact pullbackSpecIso_inv_snd K L F

end PfaffianDescent
