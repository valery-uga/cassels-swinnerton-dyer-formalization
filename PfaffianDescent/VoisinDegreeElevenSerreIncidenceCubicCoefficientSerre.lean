import PfaffianDescent.VoisinDegreeElevenSerreIncidencePulledCover
import PfaffianDescent.CubicPointTraceFieldBaseChangeNegativeTwist

/-! # Actual Serre extension on the literal coefficient-changed cubic -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceCubicCoefficientMap_affine
    {K L : Type u} [Field K] [Field L] (g : K →+* L)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    IsAffineHom (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) := by
  letI : IsAffineHom (pullback.fst (hypersurfaceToBase p hp)
      (Spec.map (CommRingCat.ofHom g))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  rw [← cubicPointTraceFieldBaseChangeCubicCoefficientMap_eq_projection]
  infer_instance

def serreIncidenceCubicCoefficientPulledSerre
    {K L : Type u} [Field K] [Field L] (g : K →+* L)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e) :
    SerreExtensionData (hypersurface (p.map g) (hp.map g))
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp)).obj N) :=
  serreIncidencePulledSerre (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) e C

def serreIncidenceCubicCoefficientPulledCover
    {K L : Type u} [Field K] [Field L] (g : K →+* L)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e) :
    SerreExtensionData.SerreExtensionRankTwoAffineCover
      (serreIncidenceCubicCoefficientPulledSerre g p hp e C) := by
  letI := serreIncidenceCubicCoefficientMap_affine g p hp
  exact serreIncidencePulledCover (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) e C

end PfaffianDescent
