import PfaffianDescent.ProjectivePositiveHomogeneousGlobalClassifyingMap
import PfaffianDescent.ProjectiveChartGlobalUniversalFamilyPullbackInjective
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Types.Basic
import AllCharacteristics.HomogeneousConfigurationQuotient

/-! The actual glued ALL-positive-homogeneous parameter scheme represents
the LITERAL relative197 finite-flat family functor on every original test.
Forward maps and whole universal family are constructed in predecessors;
recovery and derived inverse injectivity give an actual equivalence and
naturality. The original caller supplies no representability/matching/lift. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {B : Scheme.{u}} (F : Proj 𝒜 ⟶ B) (n : ℕ) [IsSeparated F]
variable (H : projectivePositiveHomogeneousChartIndex001 𝒜 → Over B)
variable (eta : ∀ a : projectivePositiveHomogeneousChartIndex001 𝒜,
  relativeFiniteFlatHilbertFunctor197 ((Proj.basicOpen 𝒜 a.val).ι ≫ F) n ≅ yoneda.obj (H a))
local notation "U𝒜" => (fun a : projectivePositiveHomogeneousChartIndex001 𝒜 => Proj.basicOpen 𝒜 (Subtype.val a))

/-- Every original test point is equivalent to a map into the actual
glued parameter object. The inverse is the literal WHOLE195/197 pullback. -/
def relativePositiveHomogeneousGlobalHilbertClassificationEquiv001 (T : Over B) :
    FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n ≃
      (T ⟶ relativeOpenChartParameterGluedObject001 F U𝒜 n H eta) where
  toFun := relativePositiveHomogeneousGlobalClassifyingMap001 𝒜 F n H eta T
  invFun := relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U𝒜 n H eta T
  left_inv P := relativePositiveHomogeneousGlobalClassifyingMap_pullback001 𝒜 F n H eta T P
  right_inv g :=
    relativeOpenChartParameterGlobalUniversalFamilyPullback_injective001 F U𝒜 n H eta T
      (relativePositiveHomogeneousGlobalClassifyingMap_pullback001 𝒜 F n H eta T
        (relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U𝒜 n H eta T g))

/-- All original slice morphisms preserve the constructed forward
classifier, DERIVED from universal pullback recovery and injectivity. -/
theorem relativePositiveHomogeneousGlobalClassifyingMap_natural001
    {T0 T1 : Over B} (a : T0 ⟶ T1)
    (P : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T1) n) :
    relativePositiveHomogeneousGlobalClassifyingMap001 𝒜 F n H eta T0
      ((relativeFiniteFlatHilbertFunctor197 F n).map a.op P) =
      a ≫ relativePositiveHomogeneousGlobalClassifyingMap001 𝒜 F n H eta T1 P := by
  apply relativeOpenChartParameterGlobalUniversalFamilyPullback_injective001 F U𝒜 n H eta T0
  let P0 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T0) n :=
    relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U𝒜 n H eta T0
      (relativePositiveHomogeneousGlobalClassifyingMap001 𝒜 F n H eta T0
        ((relativeFiniteFlatHilbertFunctor197 F n).map a.op P))
  let P1 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T0) n :=
    (relativeFiniteFlatHilbertFunctor197 F n).map a.op P
  let P2 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T0) n :=
    (relativeFiniteFlatHilbertFunctor197 F n).map a.op
      (relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U𝒜 n H eta T1
        (relativePositiveHomogeneousGlobalClassifyingMap001 𝒜 F n H eta T1 P))
  let P3 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T0) n :=
    relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U𝒜 n H eta T0
      (a ≫ relativePositiveHomogeneousGlobalClassifyingMap001 𝒜 F n H eta T1 P)
  have h01 : P0 = P1 :=
    relativePositiveHomogeneousGlobalClassifyingMap_pullback001 𝒜 F n H eta T0 _
  have h12 : P1 = P2 := congrArg
    (fun Q : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T1) n =>
      (relativeFiniteFlatHilbertFunctor197 F n).map a.op Q)
    (relativePositiveHomogeneousGlobalClassifyingMap_pullback001 𝒜 F n H eta T1 P).symm
  have h23 : P2 = P3 :=
    (relativeOpenChartParameterGlobalUniversalFamilyPullback_natural001 F U𝒜 n H eta a
      (relativePositiveHomogeneousGlobalClassifyingMap001 𝒜 F n H eta T1 P)).symm
  exact h01.trans (h12.trans h23)

/-- Genuine NatIso on ALL original tests. No global classifying datum or
matching outcome is assumed: all point maps, recovery and naturality are derived. -/
def relativePositiveHomogeneousGlobalHilbertRepresentingIso001 :
    relativeFiniteFlatHilbertFunctor197 F n ≅
      yoneda.obj (relativeOpenChartParameterGluedObject001 F U𝒜 n H eta) :=
  NatIso.ofComponents
    (fun T => (relativePositiveHomogeneousGlobalHilbertClassificationEquiv001
      𝒜 F n H eta T.unop).toIso)
    (by
      intro T0 T1 a
      apply ConcreteCategory.ext_apply
      intro P
      change relativePositiveHomogeneousGlobalClassifyingMap001 𝒜 F n H eta T1.unop
          ((relativeFiniteFlatHilbertFunctor197 F n).map a P) =
        a.unop ≫ relativePositiveHomogeneousGlobalClassifyingMap001 𝒜 F n H eta T0.unop P
      exact relativePositiveHomogeneousGlobalClassifyingMap_natural001 𝒜 F n H eta a.unop P)

/-- The inverse is EXACTLY the original whole universal-family pullback. -/
theorem relativePositiveHomogeneousGlobalHilbertRepresentingIso_inv_apply001
    (T : Over B) (g : T ⟶ relativeOpenChartParameterGluedObject001 F U𝒜 n H eta) :
    (relativePositiveHomogeneousGlobalHilbertRepresentingIso001 𝒜 F n H eta).inv.app (.op T) g =
      relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U𝒜 n H eta T g := rfl

/-- Exact full-ideal dictionary for the inverse on arbitrary original
test schemes. No radical, reduced support or new point model is substituted. -/
theorem relativePositiveHomogeneousGlobalHilbertRepresentingIso_inv_wholeIdeal001
    (T : Over B) (g : T ⟶ relativeOpenChartParameterGluedObject001 F U𝒜 n H eta) :
    ((relativePositiveHomogeneousGlobalHilbertRepresentingIso001 𝒜 F n H eta).inv.app (.op T) g).val =
      (relativeOpenChartParameterGlobalUniversalWholeIdeal001 F U𝒜 n H eta).comap
        (relativeHilbertAmbientMap197 F g) :=
  relativeOpenChartParameterGlobalUniversalFamilyPullback_wholeIdeal001 F U𝒜 n H eta T g

/-- An original family constructs a UNIQUE original-base scheme map;
both existence and uniqueness follow from the actual constructed dictionary. -/
theorem relativePositiveHomogeneousGlobalHilbertPoint_existsUnique_classifier001
    (T : Over B) (P : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n) :
    ∃! g : T ⟶ relativeOpenChartParameterGluedObject001 F U𝒜 n H eta,
      relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U𝒜 n H eta T g = P := by
  refine ⟨relativePositiveHomogeneousGlobalClassifyingMap001 𝒜 F n H eta T P,
    relativePositiveHomogeneousGlobalClassifyingMap_pullback001 𝒜 F n H eta T P, ?_⟩
  intro g hg
  exact relativeOpenChartParameterGlobalUniversalFamilyPullback_injective001 F U𝒜 n H eta T
    (hg.trans (relativePositiveHomogeneousGlobalClassifyingMap_pullback001 𝒜 F n H eta T P).symm)

/-- Actual original projective quotients over their ORIGINAL Noetherian
base construct the representing NatIso internally on ALL-positive models.
No representing object/classifier/cover/gluing/matching outcome is supplied.
Global finite presentation is a separately owned theorem. -/
def originalPositiveHomogeneousGlobalHilbertRepresentingIso001
    {R : Type u} [CommRing R] [IsNoetherianRing R] {τ : Type} [Finite τ]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule τ R))
    (n : ℕ) (hn : 0 < n) :
    relativeFiniteFlatHilbertFunctor197 (toBase I) n ≅
      yoneda.obj (Over.mk (originalPositiveHomogeneousParameterGluedToBase001 I n hn)) := by
  have hSeparated : IsSeparated
      (show Proj (grading I) ⟶ Spec (.of R) from toBase I) := isSeparated_homogeneousToBase I
  exact @relativePositiveHomogeneousGlobalHilbertRepresentingIso001
    (CoordinateRing I) inferInstance
    (Submodule R (CoordinateRing I)) inferInstance inferInstance
    (grading I) (AllCharacteristics.HomogeneousProjective.gradedRing I)
    (Spec (.of R)) (show Proj (grading I) ⟶ Spec (.of R) from toBase I) n hSeparated
    (originalPositiveHomogeneousChartIndexRepresentingObject001 I n hn)
    (originalPositiveHomogeneousChartIndexRepresentingIso001 I n hn)

end PfaffianDescent
end
