import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSupportPullback
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicCoefficientSerre
import PfaffianDescent.PullbackSourceIso

/-! # Literal retained support on the coefficient-changed cubic -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def serreIncidenceCubicSupportProjectionIso
    {K L F : Type u} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (i : Spec (.of L) ⟶ hypersurface p hp) :
    pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp) i ≅
      pullback (pullback.fst (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom (algebraMap K F)))) i :=
  pullbackTransportIso (hypersurfaceBaseChangeIso (algebraMap K F) p hp)
    (Iso.refl _) _ i _ i
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap_eq_projection
      (algebraMap K F) p hp).symm (by simp)

theorem serreIncidenceCubicSupportProjectionIso_inv_toField
    {K L F : Type u} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (i : Spec (.of L) ⟶ hypersurface p hp) :
    (serreIncidenceCubicSupportProjectionIso (F := F) p hp i).inv ≫
      pullback.fst (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp) i ≫
      hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)) =
    pullback.fst (pullback.fst (hypersurfaceToBase p hp)
      (Spec.map (CommRingCat.ofHom (algebraMap K F)))) i ≫
      pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom (algebraMap K F))) := by
  apply (Iso.inv_comp_eq (serreIncidenceCubicSupportProjectionIso (F := F) p hp i)).mpr
  rw [← Category.assoc]
  rw [serreIncidenceCubicSupportProjectionIso, pullbackTransportIso_hom_fst,
    Category.assoc, hypersurfaceBaseChangeIso_hom_snd]

def serreIncidenceCubicSupportPullbackIso
    {K L F : Type u} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (i : Spec (.of L) ⟶ hypersurface p hp)
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    Spec (.of (L ⊗[K] F)) ≅
      pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp) i :=
  serreIncidenceSupportPullbackIso (hypersurfaceToBase p hp) i hi ≪≫
    (serreIncidenceCubicSupportProjectionIso (F := F) p hp i).symm

@[reassoc]
theorem serreIncidenceCubicSupportPullbackIso_toField
    {K L F : Type u} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (i : Spec (.of L) ⟶ hypersurface p hp)
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    (serreIncidenceCubicSupportPullbackIso (F := F) p hp i hi).hom ≫
      pullback.fst (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp) i ≫
      hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)) =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := F)).toRingHom) := by
  simp only [serreIncidenceCubicSupportPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, serreIncidenceCubicSupportProjectionIso_inv_toField]
  exact serreIncidenceSupportPullbackIso_toField (hypersurfaceToBase p hp) i hi

end PfaffianDescent
