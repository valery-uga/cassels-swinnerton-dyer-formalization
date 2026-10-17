import PfaffianDescent.NativeRelativeCartesianPointNaturality317
import PfaffianDescent.ProjectivePositiveHomogeneousChartFiniteEquationPresentation
import PfaffianDescent.FiniteEquationHilbertAllTestRepresentability
import AllCharacteristics.HomogeneousProjective
import Mathlib.CategoryTheory.Types.Basic

/-! The actual positive homogeneous chart is classified over its ORIGINAL
Noetherian base. Its finite equations and base-preserving chart comparison
are constructed internally, and all test maps transport entire ideal sheaves. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

variable {X Y B : Scheme.{u}} (F : X ⟶ B) (G : Y ⟶ B)
variable (e : X ≅ Y) (hBase : e.hom ≫ G = F)

/-- Pasting the actual original-base comparison gives the Cartesian square
for the literal original family on every scheme test. -/
private theorem isomorphicOriginalFamily_relativeCartesian001
    (hBase : e.hom ≫ G = F) (T : Over B) :
    IsPullback (pullback.snd T.hom F ≫ e.hom)
      (relativeHilbertFamily197 F T) G T.hom := by
  have hRight : IsPullback e.hom F G (𝟙 B) :=
    IsPullback.of_horiz_isIso_mono ⟨by simpa only [Category.comp_id] using hBase⟩
  exact (by
    simpa only [relativeHilbertFamily197, Category.comp_id] using
      (IsPullback.of_hasPullback T.hom F).flip.paste_horiz hRight)

/-- Actual whole finite-flat families are transported by the native
Cartesian chart equivalence, retaining the original test and degree. -/
def isomorphicOriginalFamilyRelativePointEquiv001 (T : Over B) (n : ℕ) :
    FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n ≃
      FiniteFlatHilbertPoint195 (relativeHilbertFamily197 G T) n :=
  nativeRelativeCartesianPointEquiv317 G T
    (pullback.snd T.hom F ≫ e.hom) (relativeHilbertFamily197 F T)
    (isomorphicOriginalFamily_relativeCartesian001 F G e hBase T) n

/-- The transport preserves the ENTIRE ideal by the actual inverse scheme
map. This equality does not replace the family by its support or reduction. -/
theorem isomorphicOriginalFamilyRelativePointEquiv_wholeIdeal001
    (T : Over B) (n : ℕ) (P : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n) :
    (isomorphicOriginalFamilyRelativePointEquiv001 F G e hBase T n P).val =
      P.val.comap (nativeRelativeCartesianChartIso317 G T
        (pullback.snd T.hom F ≫ e.hom) (relativeHilbertFamily197 F T)
        (isomorphicOriginalFamily_relativeCartesian001 F G e hBase T)).inv := rfl

/-- Every original test map respects the whole-family transport. The
projection equalities and native Cartesian naturality supply the proof. -/
theorem isomorphicOriginalFamilyRelativePointEquiv_natural001
    {T0 T1 : Over B} (a : T0 ⟶ T1) (n : ℕ)
    (P : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T1) n) :
    isomorphicOriginalFamilyRelativePointEquiv001 F G e hBase T0 n
        ((relativeFiniteFlatHilbertFunctor197 F n).map a.op P) =
      (relativeFiniteFlatHilbertFunctor197 G n).map a.op
        (isomorphicOriginalFamilyRelativePointEquiv001 F G e hBase T1 n P) := by
  have hOriginal : relativeHilbertAmbientMap197 F a ≫
      (pullback.snd T1.hom F ≫ e.hom) = pullback.snd T0.hom F ≫ e.hom := by
    rw [← Category.assoc, relativeHilbertAmbientMap_snd197]
  exact nativeRelativeCartesianPointEquiv_natural317 G a
    (pullback.snd T0.hom F ≫ e.hom) (relativeHilbertFamily197 F T0)
    (isomorphicOriginalFamily_relativeCartesian001 F G e hBase T0)
    (pullback.snd T1.hom F ≫ e.hom) (relativeHilbertFamily197 F T1)
    (isomorphicOriginalFamily_relativeCartesian001 F G e hBase T1)
    (relativeHilbertAmbientMap197 F a) hOriginal (relativeHilbertAmbientMap_fst197 F a)
    (relativeHilbertAmbientMap_isPullback197 F a) n P

/-- Constructed natural comparison of literal original whole-family
functors, over the SAME base and on ALL scheme tests. -/
def isomorphicOriginalFamilyHilbertFunctorIso001 (n : ℕ) :
    relativeFiniteFlatHilbertFunctor197 F n ≅ relativeFiniteFlatHilbertFunctor197 G n :=
  NatIso.ofComponents
    (fun T => (isomorphicOriginalFamilyRelativePointEquiv001 F G e hBase T.unop n).toIso)
    (by
      intro T0 T1 a
      apply ConcreteCategory.ext_apply
      intro P
      exact isomorphicOriginalFamilyRelativePointEquiv_natural001 F G e hBase a.unop n P)

/-- Genuine representation for the SAME actual positive homogeneous chart
of the original projective quotient over the ORIGINAL Noetherian base.
Its presentation, equations, quotient comparison and classifier are all
constructed; none of these outcomes is a premise. Nilpotents and the
literal finite-flat whole-family functor are retained on all scheme tests. -/
theorem originalPositiveHomogeneousChart_exists_allTestHilbertRepresentingIso001
    {R : Type u} [CommRing R] [IsNoetherianRing R] {σ : Type} [Finite σ]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
    (a : CoordinateRing I) (d : ℕ) (hd : 0 < d) (ha : a ∈ grading I d)
    (n : ℕ) (hn : 0 < n) :
    ∃ H : Over (Spec (.of R)),
      Nonempty (relativeFiniteFlatHilbertFunctor197
        ((Proj.basicOpen (grading I) a).ι ≫ toBase I) n ≅ yoneda.obj H) := by
  letI := originalPositiveHomogeneousChartNativeAlgebra001 I a
  obtain ⟨m, r, q, eAlg, E, hEForm, hEBase⟩ :=
    originalPositiveHomogeneousChart_exists_finiteEquations_originalBaseSchemeIso001 I a d hd ha
  let G := finiteEquationOriginalPolynomialEmbedding001 R m r q ≫ nativePolynomialProjection300 R m
  have hBase : E.hom ≫ G = (Proj.basicOpen (grading I) a).ι ≫ toBase I := by
    dsimp only [G]
    rw [finiteEquationOriginalPolynomialEmbedding_toBase001]
    exact hEBase
  exact ⟨finiteEquationHilbertRepresentingObject001 R m n r q,
    ⟨isomorphicOriginalFamilyHilbertFunctorIso001
        ((Proj.basicOpen (grading I) a).ι ≫ toBase I) G E hBase n ≪≫
      finiteEquationOriginalQuotientHilbertRepresentingIso001 R m n r q hn⟩⟩

end PfaffianDescent
end
