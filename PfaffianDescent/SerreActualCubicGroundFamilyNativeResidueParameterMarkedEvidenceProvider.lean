import PfaffianDescent.SerreActualCubicGroundFamilyNativeMarkedConfigurationEvidenceProvider

/-! Exact native residue-field and selected-parameter specialization.
The parameter morphism is the literal Spec.map beta followed by qF; section,
incidence and configuration-point inputs are retained. No evidence is assumed. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The literal coefficient Spec map, without an auxiliary Algebra instance. -/
def serreActualNativeResidueCoefficientSpecMap
    {F E : Type u} [Field F] [Field E] (β : F →+* E) :
    Spec (.of E) ⟶ Spec (.of F) :=
  Spec.map (CommRingCat.ofHom β)

/-- The literal native selected parameter point. -/
def serreActualNativeSelectedResidueParameter
    {F E : Type u} [Field F] [Field E] (β : F →+* E)
    {P : Scheme.{u}} (qF : Spec (.of F) ⟶ P) : Spec (.of E) ⟶ P :=
  serreActualNativeResidueCoefficientSpecMap β ≫ qF

/-- Exact definitional compatibility with production Core's beta.toAlgebra
coefficient map. This is proved, never assumed as a comparison certificate. -/
theorem serreActualNativeSelectedResidueParameter_eq_algebraMap
    {F E : Type u} [Field F] [Field E] (β : F →+* E)
    {P : Scheme.{u}} (qF : Spec (.of F) ⟶ P) :
    serreActualNativeSelectedResidueParameter β qF =
      (letI : Algebra F E := β.toAlgebra
       Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ qF) := rfl

/-- Exact native E/beta/qF partial application of the accepted marked-
configuration DATA provider. Its inferred output retains the literal native
x/M/pp/B.zero, s/hsp/marked membership, abstract cA/hcfg, and point index. -/
@[irreducible]
def serreActualCubicGroundFamily_nativeResidueParameterMarkedEvidenceProvider
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
    (β : (cubicConfigurationBase p hp 3).functionField →+*
      Rk.residueField (genericPoint Rk))
    (G : Matrix (Fin 9) (Fin 3) (cubicConfigurationBase p hp 3).functionField)
    (H : Matrix (Fin 3) (Fin 9) (cubicConfigurationBase p hp 3).functionField)
    (hHG : H * G = 1)
    (qF : Spec (.of (cubicConfigurationBase p hp 3).functionField) ⟶
      scheme (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 3) (cubicConfigurationBase p hp 3).functionField))) :=
  serreActualCubicGroundFamily_nativeMarkedConfigurationEvidenceProvider
    p hp hp0 a ha ι e C h9 A B aRank G H hHG
    (E := Rk.residueField (genericPoint Rk))
    (serreActualNativeSelectedResidueParameter β qF)

end PfaffianDescent
