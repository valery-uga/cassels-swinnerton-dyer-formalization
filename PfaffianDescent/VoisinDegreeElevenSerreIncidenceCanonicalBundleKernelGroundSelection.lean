import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalBundleKernelSeedOpen
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelFieldGroundSelection

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

variable {K E : Type u} [Field K] [Field E] {X B : Scheme.{u}} [IsAffine B]
variable (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
variable [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
variable (C : SchemeModuleFiniteFreeAffineCover M (ULift.{u} (Fin 2)))
variable (b : B ⟶ Spec (.of K)) (chart : Fin 3 → C.ι)
variable (markedU : ∀ i, B ⟶ (C.U (chart i) : Scheme.{u}))
variable (hmarked : ∀ i, (markedU i ≫ (C.U (chart i)).ι) ≫ base = b)
variable (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver base M) = 9)
variable (ρ : Fin 6 ≃ (Fin 3 × ULift.{u} (Fin 2)))

variable (β : Γ(B, ⊤) →+* E) (c : Spec (.of E) ⟶ B)
variable (hc : Spec.map (CommRingCat.ofHom β) ≫ B.isoSpec.inv = c)

variable {F : Type u} [Field F] [Algebra F E] [Infinite F]

theorem serreIncidenceBundleKernel_exists_ground_selection
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
    (hHG : H * G = 1)
    (hrange : LinearMap.range (Matrix.toLin' (G.map (algebraMap F E))) =
      LinearMap.ker (Matrix.toLin'
        ((serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ).map β)))
    (honto : Function.Surjective (Matrix.toLin'
        ((serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ).map β)))
    (W : (serreIncidenceBundleKernelIdeal base M C b chart markedU hmarked).subscheme.Opens)
    (s : Spec (.of E) ⟶ (serreIncidenceBundleKernelIdeal base M C b chart markedU hmarked).subscheme)
    (hs : s ≫ serreIncidenceBundleKernelConfiguration base M C b chart markedU hmarked = c)
    (x : Spec (.of E)) (hx : s x ∈ W) :
    let e := serreThreePointSectionIncidence_nativeKernelFieldIso
      base M C b chart markedU hmarked h9 ρ β c hc
    let U := (e.hom ≫ pullback.fst
      (serreIncidenceBundleKernelConfiguration base M C b chart markedU hmarked) c) ⁻¹ᵁ W
    ∃ (qF : Spec (.of F) ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
      (q : Spec (.of E) ⟶ (U : Scheme.{u})),
      qF ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)) = 𝟙 _ ∧
      (q ≫ U.ι ≫ e.hom ≫ pullback.fst
        (serreIncidenceBundleKernelConfiguration base M C b chart markedU hmarked) c) ≫
        serreIncidenceBundleKernelConfiguration base M C b chart markedU hmarked = c ∧
      (∀ y : Spec (.of E), (q ≫ U.ι ≫ e.hom ≫ pullback.fst
        (serreIncidenceBundleKernelConfiguration base M C b chart markedU hmarked) c) y ∈ W) ∧
      q ≫ U.ι ≫ schemeQuotientMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E))
        (serreEvaluationHomogeneousIdeal
          ((serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ).map β)) bot_le ≫
        projectiveCoefficientMap (algebraMap F E)
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) F))
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E)) (by simp) =
        Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ qF ≫
          serreKernelFrameProjectiveEmbedding G H hHG := by
  exact serreIncidenceKernelField_exists_ground_selection
    (serreIncidenceBundleKernelConfiguration base M C b chart markedU hmarked) c
    ((serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ).map β)
    (serreThreePointSectionIncidence_nativeKernelFieldIso
      base M C b chart markedU hmarked h9 ρ β c hc)
    (serreThreePointSectionIncidence_nativeKernelFieldIso_toBase
      base M C b chart markedU hmarked h9 ρ β c hc)
    G H hHG hrange honto W s hs x hx

end PfaffianDescent
