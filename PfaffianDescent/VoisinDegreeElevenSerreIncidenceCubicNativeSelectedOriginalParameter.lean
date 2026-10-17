import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicNativeGroundRankSelection
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalBundleGroundFrameParameters
import PfaffianDescent.VoisinFieldBaseChangePointEvaluation

/-! Actual SAME-G selected kernel points have the original canonical
section parameter predicted by the ground plane. All coefficient scalars
and configuration-base compatibility are derived internally. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
variable {K E : Type u} [Field K] [Field E]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
variable [hB : IsIntegral (cubicConfigurationBase p hp 3)]
local instance : IsIntegral (projectiveConfigurationQuotientOpen
    (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) 3).toScheme := hB
variable [hordered : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
local instance : IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 3).left := hordered
variable (c : Spec (.of E) ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
variable (β : (cubicConfigurationBase p hp 3).functionField →+* E)
variable (hβ : Spec.map (CommRingCat.ofHom β) ≫
    (cubicConfigurationBase p hp 3).fromSpecStalk
      (genericPoint (cubicConfigurationBase p hp 3)) =
    c ≫ configurationQuotientMap (equationIdeal p hp) 3)
variable (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
variable (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫
    cubicConfigurationToBase p hp 3)


open ProjectiveNegativeTwist

include hβ ha

/-- Evaluating actual base constants at the lifted native rank chart point
uses exactly the composite K→F→E coefficient map. -/
theorem serreIncidenceCubicNativeRank_fieldPoint_baseCoeff
    {A : Scheme.{u}}
    (aRank : A ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    (cA : Spec (.of E) ⟶ A) (hcA : cA ≫ aRank = c) :
    (fieldPointΓevaluation cA).comp
      (affineFunctionHom
        (aRank ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).hom)) =
      β.comp a.hom := by
  have hbase : c ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).hom =
      Spec.map (CommRingCat.ofHom (β.comp a.hom)) := by
    simpa only [Category.assoc, orderedFamilyCoordinate_toBase,
      (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).w] using
      (pointSplittingCubicSerrePulledEvaluation_original_base p hp c β hβ a ha (0 : Fin 3))
  have hcbase : cA ≫ (aRank ≫
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).hom) =
      Spec.map (CommRingCat.ofHom (β.comp a.hom)) := by
    simpa only [← Category.assoc, hcA] using hbase
  ext k
  simp only [RingHom.comp_apply]
  have h := fieldPointΓevaluation_comp cA
    (aRank ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).hom)
    ((Scheme.ΓSpecIso (.of K)).inv.hom k)
  change fieldPointΓevaluation (cA ≫ (aRank ≫
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).hom))
      ((Scheme.ΓSpecIso (.of K)).inv.hom k) =
    fieldPointΓevaluation cA (affineFunctionHom (aRank ≫
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).hom) k) at h
  rw [← h, hcbase]
  exact fieldPointΓevaluation_Spec_map (β.comp a.hom) k

/-- Given the exact SAME-G coefficient equality returned by native ground
selection, derive the old incidence seed's canonical parameter equality.
The remaining arguments are G/H/hHG/qF/q/hframe; for a selected open point
use q = qSelected≫U.ι. The result type is inferred from the checked generic
parameter theorem, retaining the actual native kernel-field isomorphism.
Its RHS is the expanded actual ground-plane original-parameter map. -/
@[irreducible]
def serreIncidenceCubicNativeRank_selected_originalParameter
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    {A : Scheme.{u}} [IsAffine A]
    (aRank : A ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    (chart : Fin 3 → C.ι) (marked : ∀ i, A ⟶ (C.U (chart i)).toScheme)
    (hmarked : ∀ i, marked i ≫ (C.U (chart i)).ι =
      (aRank ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 i).left)
    (cA : Spec (.of E) ⟶ A) (hcA : cA ≫ aRank = c)
    (ρ : Fin 6 ≃ (Fin 3 × ULift.{u} (Fin 2))) :=
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  letI : Algebra F E := β.toAlgebra
  letI : Algebra K E := (β.comp a.hom).toAlgebra
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun k => rfl)
  let b := aRank ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).hom
  let hb := serreIncidenceCubicNativeRank_marked_toBase p hp e C aRank chart marked hmarked
  let Cv := serreIncidenceRankTwoAffineCover e C
  fun G H hHG qF q hframe =>
    serreIncidenceBundleGroundFrame_toOriginalParameters (F := F)
      (hypersurfaceToBase p hp) e.E Cv b chart marked hb h9 ρ
      (fieldPointΓevaluation cA) cA (serreIncidenceAffineFieldPoint_spec cA)
      G H hHG qF q
      (serreIncidenceCubicNativeRank_fieldPoint_baseCoeff p hp c β hβ a ha aRank cA hcA)
      hframe

end PfaffianDescent
