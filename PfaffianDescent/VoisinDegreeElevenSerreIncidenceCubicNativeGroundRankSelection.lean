import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicNativeGroundRankOpen
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicOriginalNativeBundleMatrix
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalBundleKernelGroundSelection
import PfaffianDescent.VoisinDegreeElevenSerreIncidencePlaneFieldPoint

/-! # Actual cubic incidence seeds select parameters in the native ground kernel -/
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

/-- The marked maps in a native cubic rank chart lie over the actual
ordered configuration base; the base compatibility is derived from their
literal coordinate factorizations. -/
theorem serreIncidenceCubicNativeRank_marked_toBase
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    {A : Scheme.{u}}
    (aRank : A ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    (chart : Fin 3 → C.ι) (marked : ∀ i, A ⟶ (C.U (chart i)).toScheme)
    (hmarked : ∀ i, marked i ≫ (C.U (chart i)).ι =
      (aRank ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 i).left) :
    ∀ i, (marked i ≫ (C.U (chart i)).ι) ≫ hypersurfaceToBase p hp =
      aRank ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).hom := by
  intro i
  rw [hmarked i, Category.assoc, orderedFamilyCoordinate_toBase,
    Category.assoc, (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).w]

include β hβ a ha

/-- An actual seed in a canonical bundle-incidence open selects a ground
parameter in the same native unordered kernel frame. All rank, kernel range,
marked-base, and matrix-surjectivity inputs are derived internally. -/
theorem serreIncidenceCubicNativeRank_exists_ground_selection
    [Infinite (cubicConfigurationBase p hp 3).functionField]
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
    (m : (Fin 3 × ULift.{u} (Fin 2)) ↪ Fin 9)
    (hm : IsUnit (Matrix.det (Matrix.submatrix
      (serreIncidenceNativeAffineEvaluationMatrix (hypersurfaceToBase p hp) e C h9 chart marked) id m)))
    (cA : Spec (.of E) ⟶ A) (hcA : cA ≫ aRank = c)
    (ρ : Fin 6 ≃ (Fin 3 × ULift.{u} (Fin 2))) :
    let b := aRank ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).hom
    let hb := serreIncidenceCubicNativeRank_marked_toBase p hp e C aRank chart marked hmarked
    let Cv := serreIncidenceRankTwoAffineCover e C
    ∀ (W : (serreIncidenceBundleKernelIdeal (hypersurfaceToBase p hp) e.E Cv
        b chart marked hb).subscheme.Opens)
      (s : Spec (.of E) ⟶ (serreIncidenceBundleKernelIdeal (hypersurfaceToBase p hp) e.E Cv
        b chart marked hb).subscheme)
      (hs : s ≫ serreIncidenceBundleKernelConfiguration (hypersurfaceToBase p hp) e.E Cv
        b chart marked hb = cA)
      (x : Spec (.of E)) (_hx : s x ∈ W),
    let F : Type u := (cubicConfigurationBase p hp 3).functionField
    letI : Algebra F E := β.toAlgebra
    let eK := serreThreePointSectionIncidence_nativeKernelFieldIso
      (hypersurfaceToBase p hp) e.E Cv b chart marked hb h9 ρ
      (fieldPointΓevaluation cA) cA (serreIncidenceAffineFieldPoint_spec cA)
    let U := (eK.hom ≫ pullback.fst
      (serreIncidenceBundleKernelConfiguration (hypersurfaceToBase p hp) e.E Cv
        b chart marked hb) cA) ⁻¹ᵁ W
    ∃ (h3 : Module.finrank F
      (LinearMap.ker (serreIncidenceCubicNativeGroundRestriction p hp a ha e C)) = 3)
      (H : Matrix (Fin 3) (Fin 9) F)
      (hHG : H * serreIncidenceCubicNativeGroundKernelMatrix p hp a ha e C h9 h3 = 1)
      (qF : Spec (.of F) ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
      (q : Spec (.of E) ⟶ (U : Scheme.{u})),
      qF ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)) = 𝟙 _ ∧
      (q ≫ U.ι ≫ eK.hom ≫ pullback.fst
        (serreIncidenceBundleKernelConfiguration (hypersurfaceToBase p hp) e.E Cv
          b chart marked hb) cA) ≫
        serreIncidenceBundleKernelConfiguration (hypersurfaceToBase p hp) e.E Cv
          b chart marked hb = cA ∧
      (∀ y : Spec (.of E), (q ≫ U.ι ≫ eK.hom ≫ pullback.fst
        (serreIncidenceBundleKernelConfiguration (hypersurfaceToBase p hp) e.E Cv
          b chart marked hb) cA) y ∈ W) ∧
      q ≫ U.ι ≫ schemeQuotientMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E))
        (serreEvaluationHomogeneousIdeal
          ((serreIncidenceBundleKernelMatrix (hypersurfaceToBase p hp) e.E Cv
            chart marked h9 ρ).map (fieldPointΓevaluation cA))) bot_le ≫
        projectiveCoefficientMap (algebraMap F E)
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) F))
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E)) (by simp) =
        Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ qF ≫
          serreKernelFrameProjectiveEmbedding
            (serreIncidenceCubicNativeGroundKernelMatrix p hp a ha e C h9 h3) H hHG := by
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra F E := β.toAlgebra
  dsimp only
  intro W s hs x hx
  obtain ⟨h3, H, hHG, hrange⟩ := serreIncidenceCubicNativeRank_exists_ground_kernel_range
    p hp c β hβ a ha e C h9 aRank chart marked hmarked m hm cA hcA ρ
  have honto := serreIncidenceCubicNativeRank_original_matrix_surjective
    p hp c β hβ a ha e C h9 aRank chart marked hmarked m hm cA hcA ρ
  rw [serreIncidenceCubicOriginalNativeMatrix_eq_bundle p hp e C h9 chart marked cA ρ]
    at hrange honto
  obtain ⟨qF, q, hF, hC, hW, hcoeff⟩ :=
    serreIncidenceBundleKernel_exists_ground_selection (F := F)
      (hypersurfaceToBase p hp) e.E (serreIncidenceRankTwoAffineCover e C)
      (aRank ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).hom)
      chart marked
      (serreIncidenceCubicNativeRank_marked_toBase p hp e C aRank chart marked hmarked)
      h9 ρ (fieldPointΓevaluation cA) cA (serreIncidenceAffineFieldPoint_spec cA)
      (serreIncidenceCubicNativeGroundKernelMatrix p hp a ha e C h9 h3) H hHG
      hrange honto W s hs x hx
  exact ⟨h3, H, hHG, qF, q, hF, hC, hW, hcoeff⟩

end PfaffianDescent
