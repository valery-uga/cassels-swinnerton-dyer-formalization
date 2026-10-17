import PfaffianDescent.SerreActualCubicGroundFamilyNativeSectionEvidenceProvider

/-! Exact native rank-chart configuration and marked-point specialization of
the accepted section-evidence provider. Remaining incidence and section inputs
are retained, and no evidence record is assumed. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def serreActualNativeRankConfiguration
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {Rk : Scheme.{u}}
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left) :
    Rk ⟶ Spec (.of K) :=
  aRank ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).hom

def serreActualNativeRankMarked
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {Rk : Scheme.{u}}
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left) :
    Fin 3 → (Rk ⟶ hypersurface p hp) := fun n =>
  aRank ≫ (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left ≫
    (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 n).left

theorem serreActualNativeRankMarked_toBase
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {Rk : Scheme.{u}}
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left) :
    ∀ n, serreActualNativeRankMarked p hp aRank n ≫ hypersurfaceToBase p hp =
      serreActualNativeRankConfiguration p hp aRank := fun n => by
  simp only [serreActualNativeRankMarked, serreActualNativeRankConfiguration,
    Category.assoc, orderedFamilyCoordinate_toBase,
    (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).w]

/-- Exact partial DATA specialization. The remaining inferred result is the
original s/hsp/hs/cA/hcfg/n provider, with precisely the native Evidence index. -/
@[irreducible]
def serreActualCubicGroundFamily_nativeMarkedConfigurationEvidenceProvider
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
    [IsIntegral (cubicConfigurationBase p hp 3)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫ cubicConfigurationToBase p hp 3)
    {D : Scheme.{u}} [IsAffine D]
    (ι : D ⟶ hypersurface p hp) [IsClosedImmersion ι]
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    {IA IB : Type u} [Fintype IA] [DecidableEq IA] [Fintype IB] [DecidableEq IB]
    (A : SchemeModuleFiniteFreeAffineCover e.E IA)
    (B : letI : Algebra K (cubicConfigurationBase p hp 3).functionField := a.hom.toAlgebra
      SchemeModuleFiniteFreeAffineCover
        ((Scheme.Modules.pullback
          (cubicPointTraceFieldBaseChangeCubicCoefficientMap
            (algebraMap K (cubicConfigurationBase p hp 3).functionField) p hp)).obj e.E) IB)
    {Rk : Scheme.{u}} [IsIntegral Rk]
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    [IsOpenImmersion aRank]
    (G : Matrix (Fin 9) (Fin 3) (cubicConfigurationBase p hp 3).functionField)
    (H : Matrix (Fin 3) (Fin 9) (cubicConfigurationBase p hp 3).functionField)
    (hHG : H * G = 1)
    {E : Type u} [Field E]
    (bE : Spec (.of E) ⟶ scheme (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 3) (cubicConfigurationBase p hp 3).functionField))) :=
  serreActualCubicGroundFamily_nativeSectionEvidenceProvider
    p hp hp0 a ha ι e C h9 A B G H hHG (Cfg := Rk) (E := E) bE
    (serreActualNativeRankConfiguration p hp aRank)
    (serreActualNativeRankMarked p hp aRank)
    (serreActualNativeRankMarked_toBase p hp aRank)

end PfaffianDescent
