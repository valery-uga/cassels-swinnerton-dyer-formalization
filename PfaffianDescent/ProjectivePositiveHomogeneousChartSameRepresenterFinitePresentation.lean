import PfaffianDescent.FiniteEquationHilbertNoetherianFinitePresentation
import PfaffianDescent.ProjectivePositiveHomogeneousChartAllTestClassifier
import Mathlib.CategoryTheory.Yoneda

/-! LFP for the SAME already constructed all-test original chart
representer, through its genuine Yoneda comparison over ORIGINAL SpecR. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Pure original-base property transport; the actual model LFP is
constructed by the finite-equation leaf in the natural caller below. -/
private theorem originalRepresenterOverIso_lfp_transport001
    {R : Type u} [CommRing R] (H J : Over (Spec (.of R))) (E : H ≅ J)
    (hJ : LocallyOfFinitePresentation J.hom) : LocallyOfFinitePresentation H.hom := by
  let e : H.left ≅ J.left := (Over.forget (Spec (.of R))).mapIso E
  have hBase : e.hom ≫ J.hom = H.hom := E.hom.w
  letI : LocallyOfFinitePresentation J.hom := hJ
  have hComposite : LocallyOfFinitePresentation (e.hom ≫ J.hom) := inferInstance
  rw [hBase] at hComposite
  exact hComposite

/-- Derive LFP of THIS exact original chart representer H and classifier
eta. A finite-equation model and its LFP are constructed internally, then
Yoneda produces an isomorphism in the original slice. No replacement H,
reduced ideal, LFP conclusion, or base-changing isomorphism is an input. -/
theorem originalPositiveHomogeneousChart_sameAllTestHilbertRepresenter_locallyOfFinitePresentation001
    {R : Type u} [CommRing R] [IsNoetherianRing R] {sigma : Type} [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma R))
    (a : CoordinateRing I) (d : ℕ) (hd : 0 < d) (ha : a ∈ grading I d)
    (n : ℕ) (hn : 0 < n) (H : Over (Spec (.of R)))
    (eta : relativeFiniteFlatHilbertFunctor197
      ((Proj.basicOpen (grading I) a).ι ≫ toBase I) n ≅ yoneda.obj H) :
    LocallyOfFinitePresentation H.hom := by
  letI := originalPositiveHomogeneousChartNativeAlgebra001 I a
  obtain ⟨m, r, q, eAlg, E, hEForm, hEBase⟩ :=
    originalPositiveHomogeneousChart_exists_finiteEquations_originalBaseSchemeIso001 I a d hd ha
  let G := finiteEquationOriginalPolynomialEmbedding001 R m r q ≫ nativePolynomialProjection300 R m
  have hBase : E.hom ≫ G = (Proj.basicOpen (grading I) a).ι ≫ toBase I := by
    dsimp only [G]
    rw [finiteEquationOriginalPolynomialEmbedding_toBase001]
    exact hEBase
  let model : Over (Spec (.of R)) := finiteEquationHilbertRepresentingObject001 R m n r q
  let etaModel : relativeFiniteFlatHilbertFunctor197
      ((Proj.basicOpen (grading I) a).ι ≫ toBase I) n ≅ yoneda.obj model :=
    isomorphicOriginalFamilyHilbertFunctorIso001
      ((Proj.basicOpen (grading I) a).ι ≫ toBase I) G E hBase n ≪≫
      finiteEquationOriginalQuotientHilbertRepresentingIso001 R m n r q hn
  let EOver : H ≅ model := Yoneda.fullyFaithful.preimageIso (eta.symm ≪≫ etaModel)
  exact originalRepresenterOverIso_lfp_transport001 H model EOver
    (finiteEquationHilbertRepresentingObject_locallyOfFinitePresentation001 R m n r q)

/-- Original Noetherian positive homogeneous chart data constructs ONE
actual all-test representing object and classifier, then proves LFP of
THAT SAME object's original R morphism. No representing/LFP outcome input. -/
theorem originalPositiveHomogeneousChart_exists_sameAllTestHilbertRepresenter_lfp001
    {R : Type u} [CommRing R] [IsNoetherianRing R] {sigma : Type} [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma R))
    (a : CoordinateRing I) (d : ℕ) (hd : 0 < d) (ha : a ∈ grading I d)
    (n : ℕ) (hn : 0 < n) :
    ∃ (H : Over (Spec (.of R)))
      (eta : relativeFiniteFlatHilbertFunctor197
        ((Proj.basicOpen (grading I) a).ι ≫ toBase I) n ≅ yoneda.obj H),
      LocallyOfFinitePresentation H.hom := by
  obtain ⟨H, ⟨eta⟩⟩ :=
    originalPositiveHomogeneousChart_exists_allTestHilbertRepresentingIso001 I a d hd ha n hn
  exact ⟨H, eta,
    originalPositiveHomogeneousChart_sameAllTestHilbertRepresenter_locallyOfFinitePresentation001
      I a d hd ha n hn H eta⟩

end PfaffianDescent
end
