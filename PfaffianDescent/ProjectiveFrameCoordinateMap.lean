import PfaffianDescent.ProjectiveFrameTransition
import PfaffianDescent.PolynomialProjectiveMap
import PfaffianDescent.RectangularSubstitution
import AllCharacteristics.ProjectiveBaseChange
import AllCharacteristics.ProjectiveCoefficientComposition

/-!
# Projective morphisms from invertible frame-coordinate changes

An invertible matrix of frame coordinates induces an actual morphism of the
corresponding relative projective spaces.  These maps are the scheme-level
overlap transitions for the local Grassmannian-frame families.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {R : Type u} [CommRing R] {m : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The relative projective coordinate space of a finite frame. -/
noncomputable abbrev projectiveFrameCoordinateSpace (m : ℕ) : Scheme.{u} :=
  scheme (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) R))

/-- Change of coefficient rings for a frame-coordinate projective space. -/
noncomputable def projectiveFrameCoordinateCoefficientMap
    {S : Type u} [CommRing S] (f : R →+* S) :
    projectiveFrameCoordinateSpace (R := S) m ⟶
      projectiveFrameCoordinateSpace (R := R) m :=
  projectiveCoefficientMap f
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) R))
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) S))
    (by simp)

/-- Frame-coordinate coefficient base change commutes with the structural
maps to the two affine coefficient spectra. -/
theorem projectiveFrameCoordinateCoefficientMap_toBase
    {S : Type u} [CommRing S] (f : R →+* S) :
    projectiveFrameCoordinateCoefficientMap (m := m) f ≫
      toBase (⊥ : HomogeneousIdeal
        (MvPolynomial.homogeneousSubmodule (Fin m) R)) =
      toBase (⊥ : HomogeneousIdeal
        (MvPolynomial.homogeneousSubmodule (Fin m) S)) ≫
        Spec.map (CommRingCat.ofHom f) := by
  exact projectiveCoefficientMap_toBase f
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) R))
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) S))
    (by simp)

/-- Frame-coordinate coefficient changes compose in the same order as their
affine coefficient-ring maps. -/
theorem projectiveFrameCoordinateCoefficientMap_comp
    {S T : Type u} [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    projectiveFrameCoordinateCoefficientMap (m := m) g ≫
      projectiveFrameCoordinateCoefficientMap (m := m) f =
        projectiveFrameCoordinateCoefficientMap (m := m) (g.comp f) := by
  unfold projectiveFrameCoordinateCoefficientMap
  simpa using projectiveCoefficientMap_comp f g
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) R))
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) S))
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) T))
    (by simp) (by simp)

theorem projectiveFrameCoordinateCoefficientMap_id :
    projectiveFrameCoordinateCoefficientMap (m := m) (RingHom.id R) = 𝟙 _ := by
  unfold projectiveFrameCoordinateCoefficientMap
  exact projectiveCoefficientMap_id _

/-- Base change of a frame-coordinate projective space along an open affine
map is an open immersion. -/
instance projectiveFrameCoordinateCoefficientMap_isOpenImmersion
    {S : Type u} [CommRing S] (f : R →+* S)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))] :
    IsOpenImmersion (projectiveFrameCoordinateCoefficientMap (m := m) f) := by
  unfold projectiveFrameCoordinateCoefficientMap
  apply MorphismProperty.of_isPullback
    (isPullback_projectiveCoefficientMap f
      (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) R))
      (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) S))
      (by simp)).flip
  infer_instance

/-- Coefficient base change of a frame-coordinate projective space along an
affine isomorphism is an isomorphism. -/
instance projectiveFrameCoordinateCoefficientMap_isIso
    {S : Type u} [CommRing S] (f : R →+* S)
    [IsIso (Spec.map (CommRingCat.ofHom f))] :
    IsIso (projectiveFrameCoordinateCoefficientMap (m := m) f) := by
  unfold projectiveFrameCoordinateCoefficientMap
  apply MorphismProperty.of_isPullback
    (isPullback_projectiveCoefficientMap f
      (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) R))
      (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) S))
      (by simp)).flip
  infer_instance

/-- An invertible coordinate substitution induces an actual morphism of
relative projective frame-coordinate spaces. -/
noncomputable def projectiveFrameCoordinateMap
    (M N : Matrix (Fin m) (Fin m) R) (hNM : N * M = 1) :
    projectiveFrameCoordinateSpace (R := R) m ⟶
      projectiveFrameCoordinateSpace (R := R) m :=
  polynomialProjectiveMap
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) R))
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) R))
    (rectangularSubstitution M) bot_le
    (fun _d _p hp => rectangularSubstitution_homogeneous M hp)
    (rectangularSubstitution_surjective M N hNM)

instance projectiveFrameCoordinateMap_isClosedImmersion
    (M N : Matrix (Fin m) (Fin m) R) (hNM : N * M = 1) :
    IsClosedImmersion (projectiveFrameCoordinateMap M N hNM) := by
  unfold projectiveFrameCoordinateMap
  exact polynomialProjectiveMap_isClosedImmersion _ _ _ _ _ _

/-- Frame-coordinate substitutions are morphisms over their coefficient
base. -/
theorem projectiveFrameCoordinateMap_toBase
    (M N : Matrix (Fin m) (Fin m) R) (hNM : N * M = 1) :
    projectiveFrameCoordinateMap M N hNM ≫
      toBase (⊥ : HomogeneousIdeal
        (MvPolynomial.homogeneousSubmodule (Fin m) R)) =
      toBase (⊥ : HomogeneousIdeal
        (MvPolynomial.homogeneousSubmodule (Fin m) R)) := by
  exact polynomialProjectiveMap_toBase _ _ _ _ _ _

/-- Mutually inverse coordinate matrices induce mutually inverse projective
coordinate morphisms. -/
theorem projectiveFrameCoordinateMap_comp
    (M N : Matrix (Fin m) (Fin m) R)
    (hNM : N * M = 1) (hMN : M * N = 1) :
    projectiveFrameCoordinateMap N M hMN ≫
      projectiveFrameCoordinateMap M N hNM = 𝟙 _ := by
  let I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) R) := ⊥
  let F := polynomialQuotientGradingMap I I (rectangularSubstitution M) bot_le
    (fun _d _p hp => rectangularSubstitution_homogeneous M hp)
  let G := polynomialQuotientGradingMap I I (rectangularSubstitution N) bot_le
    (fun _d _p hp => rectangularSubstitution_homogeneous N hp)
  let hF := gradedSurjective_irrelevant_le F
    (polynomialQuotientGradingMap_surjective I I (rectangularSubstitution M) bot_le
      (fun _d _p hp => rectangularSubstitution_homogeneous M hp)
      (rectangularSubstitution_surjective M N hNM))
  let hG := gradedSurjective_irrelevant_le G
    (polynomialQuotientGradingMap_surjective I I (rectangularSubstitution N) bot_le
      (fun _d _p hp => rectangularSubstitution_homogeneous N hp)
      (rectangularSubstitution_surjective N M hMN))
  have hGF : G.comp F = GradedRingHom.id (grading I) := by
    dsimp [F, G]
    apply GradedRingHom.ext
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk ⊥
      (rectangularSubstitution N (rectangularSubstitution M p)) = _
    rw [← AlgHom.comp_apply, rectangularSubstitution_comp, hMN,
      rectangularSubstitution_one]
    rfl
  have hcomp := Proj.map_comp F G hF hG
  have hleft : Proj.map (G.comp F) (HomogeneousIdeal.irrelevant_le_map_comp hF hG) =
      𝟙 (Proj (grading I)) := by
    simpa only [hGF] using (Proj.map_id (𝒜 := grading I))
  have hright : Proj.map G hG ≫ Proj.map F hF = 𝟙 (Proj (grading I)) :=
    hcomp.symm.trans hleft
  change Proj.map G hG ≫ Proj.map F hF = 𝟙 (Proj (grading I))
  exact hright

section FrameTransitions

variable {V : Type*} [AddCommGroup V] [Module R V]

/-- The projective coordinate transition induced by two finite frames with
the same span. -/
noncomputable def projectiveFrameProjectiveTransition
    (q r : Fin m → V) (retractQ retractR : V →ₗ[R] (Fin m → R))
    (hretractQ : retractQ.comp (projectiveFrameMap q) = LinearMap.id)
    (hretractR : retractR.comp (projectiveFrameMap r) = LinearMap.id)
    (hspan : Submodule.span R (Set.range q) = Submodule.span R (Set.range r)) :
    projectiveFrameCoordinateSpace (R := R) m ⟶
      projectiveFrameCoordinateSpace (R := R) m :=
  projectiveFrameCoordinateMap
    (LinearMap.toMatrix' (projectiveFrameTransition q r retractR))
    (LinearMap.toMatrix' (projectiveFrameTransition r q retractQ))
    (projectiveFrameTransition_toMatrix_mul q r retractQ retractR
      hretractQ hretractR hspan)

/-- Projective coordinate transitions of equal free frames are mutually
inverse. -/
theorem projectiveFrameProjectiveTransition_comp
    (q r : Fin m → V) (retractQ retractR : V →ₗ[R] (Fin m → R))
    (hretractQ : retractQ.comp (projectiveFrameMap q) = LinearMap.id)
    (hretractR : retractR.comp (projectiveFrameMap r) = LinearMap.id)
    (hspan : Submodule.span R (Set.range q) = Submodule.span R (Set.range r)) :
    projectiveFrameProjectiveTransition r q retractR retractQ hretractR hretractQ hspan.symm ≫
      projectiveFrameProjectiveTransition q r retractQ retractR hretractQ hretractR hspan =
        𝟙 _ := by
  let M := LinearMap.toMatrix' (projectiveFrameTransition q r retractR)
  let N := LinearMap.toMatrix' (projectiveFrameTransition r q retractQ)
  have hNM : N * M = 1 := projectiveFrameTransition_toMatrix_mul
    q r retractQ retractR hretractQ hretractR hspan
  have hMN : M * N = 1 := projectiveFrameTransition_toMatrix_mul
    r q retractR retractQ hretractR hretractQ hspan.symm
  exact projectiveFrameCoordinateMap_comp M N hNM hMN

end FrameTransitions

end PfaffianDescent
