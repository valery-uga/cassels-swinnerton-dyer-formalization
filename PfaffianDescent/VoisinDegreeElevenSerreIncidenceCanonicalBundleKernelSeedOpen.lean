import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalBundleKernelFieldIso
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelFieldSeedOpen
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelBaseChange

/-! # Actual bundle section-incidence fibre and its native specialized kernel Proj -/
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

theorem serreIncidenceBundleKernelFieldOpen_nonempty_of_seed
    (W : (serreIncidenceBundleKernelIdeal base M C b chart markedU hmarked).subscheme.Opens)
    (s : Spec (.of E) ⟶ (serreIncidenceBundleKernelIdeal base M C b chart markedU hmarked).subscheme)
    (hs : s ≫ serreIncidenceBundleKernelConfiguration base M C b chart markedU hmarked = c)
    (x : Spec (.of E)) (hx : s x ∈ W) :
    ((((serreThreePointSectionIncidence_nativeKernelFieldIso
      base M C b chart markedU hmarked h9 ρ β c hc).hom ≫
      pullback.fst (serreIncidenceBundleKernelConfiguration base M C b chart markedU hmarked) c) ⁻¹ᵁ W) : Set (scheme (serreEvaluationHomogeneousIdeal
        ((serreIncidenceBundleKernelMatrix base M C chart markedU h9 ρ).map β)))).Nonempty :=
  serreIncidenceKernelFieldOpen_nonempty_of_seed
    (serreIncidenceBundleKernelConfiguration base M C b chart markedU hmarked) c
    (serreThreePointSectionIncidence_nativeKernelFieldIso
      base M C b chart markedU hmarked h9 ρ β c hc) W s hs x hx

end PfaffianDescent
