import PfaffianDescent.SerreActualCubicGroundFamilyNativeSelectedResidualCaller

/-! Consume the checked native residual as its actual degree-eight cycle
before applying it to deeply nested chosen Serre data. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreActualCubicGroundFamily_retainedGenericGood_nativeSelectedEffectiveEight
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
    [IsIntegral (cubicConfigurationBase p hp 3)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫ cubicConfigurationToBase p hp 3)
    (ι : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion ι]
    (hι : ι ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hL : finrank K L = 11)
    (e : SerreExtensionData (hypersurface p hp)
      (closedImmersionIdealTwist ι (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    {Rk : Scheme.{u}} [IsAffine Rk] [IsIntegral Rk]
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    [IsOpenImmersion aRank]
    [IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
    (chart : Fin 3 → C.ι)
    (markedU : ∀ n, Rk ⟶ (C.U (chart n)).toScheme)
    (hmarkedU : ∀ n, markedU n ≫ (C.U (chart n)).ι =
      (aRank ≫ (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 n).left)
    (minor : (Fin 3 × ULift.{u} (Fin 2)) ↪ Fin 9)
    (hminor : IsUnit (Matrix.det (Matrix.submatrix
      (serreIncidenceNativeAffineEvaluationMatrix (hypersurfaceToBase p hp)
        e C h9 chart markedU) id minor)))
    (hInitial : SerreActualConfigurationGenericGoodAtChart
      (hypersurfaceToBase p hp) e C
      (aRank ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).hom)
      chart markedU
      (serreIncidenceCubicNativeRank_marked_toBase p hp e C aRank chart markedU hmarkedU)) :
    let F := (cubicConfigurationBase p hp 3).functionField
    letI : Algebra K F := a.hom.toAlgebra
    ∃ z : EffectiveZeroCycle (hypersurface (p.map a.hom) (hp.map a.hom)),
      EffectiveZeroCycle.degree (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) z = 8 := by
  let F := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  obtain ⟨R₈, hR₈⟩ :=
    serreActualCubicGroundFamily_retainedGenericGood_nativeSelectedResidualEight
      (K := K) (L := L) p hp hp0 a ha ι hι hL e C h9 aRank
      chart markedU hmarkedU minor hminor hInitial
  exact ⟨finiteSubschemeDatumCycle
    (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R₈, hR₈.2⟩

end PfaffianDescent
