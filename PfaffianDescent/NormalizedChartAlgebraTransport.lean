import PfaffianDescent.LinearNormalizedProjectivePoint
import AllCharacteristics.HomogeneousProjectiveAmbient

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A normalized chart together with its map to ambient projective space. -/
structure NormalizedAmbientChart
    (F A : Type u) [Field F] [CommRing A] [Algebra F A]
    (σ : Type) [Finite σ]
    (I : HomogeneousIdeal (homogeneousSubmodule σ F))
    (t : Spec (.of A) ⟶ Proj (homogeneousSubmodule σ F)) where
  ell : MvPolynomial σ F
  hell : ell.IsHomogeneous 1
  x : σ → A
  he : ∀ q ∈ I.toIdeal, q.eval₂ (algebraMap F A) x = 0
  hellOne : (Ideal.Quotient.lift I.toIdeal
    (eval₂Hom (algebraMap F A) x) he)
      (Ideal.Quotient.mk I.toIdeal ell) = 1
  hpoint : linearNormalizedPointAt I x he
      (Ideal.Quotient.mk I.toIdeal ell)
      (polynomial_class_mem_grading I ell hell) hellOne ≫
      quotientProjMap I = t

/-- A normalized ambient chart on which a specified equation vanishes. -/
structure NormalizedAmbientEquationChart
    (F A : Type u) [Field F] [CommRing A] [Algebra F A]
    (σ : Type) [Finite σ]
    (I : HomogeneousIdeal (homogeneousSubmodule σ F))
    (t : Spec (.of A) ⟶ Proj (homogeneousSubmodule σ F))
    (p : MvPolynomial σ F) where
  chart : NormalizedAmbientChart F A σ I t
  equationZero : p.eval₂ (algebraMap F A) chart.x = 0

noncomputable def NormalizedAmbientEquationChart.transport
    {F A : Type u} [Field F] [CommRing A]
    {σ : Type} [Finite σ]
    (B₁ B₂ : Algebra F A) (hB : B₁ = B₂)
    (I : HomogeneousIdeal (homogeneousSubmodule σ F))
    (t : Spec (.of A) ⟶ Proj (homogeneousSubmodule σ F))
    (p : MvPolynomial σ F)
    (T : @NormalizedAmbientEquationChart F A _ _ B₁ σ _ I t p) :
    @NormalizedAmbientEquationChart F A _ _ B₂ σ _ I t p := by
  subst B₂
  exact T

/-- A normalized ambient chart on which every equation of a homogeneous
ideal vanishes. -/
structure NormalizedAmbientIdealChart
    (F A : Type u) [Field F] [CommRing A] [Algebra F A]
    (σ : Type) [Finite σ]
    (I : HomogeneousIdeal (homogeneousSubmodule σ F))
    (t : Spec (.of A) ⟶ Proj (homogeneousSubmodule σ F))
    (C : HomogeneousIdeal (homogeneousSubmodule σ F)) where
  chart : NormalizedAmbientChart F A σ I t
  idealZero : ∀ q ∈ C.toIdeal, q.eval₂ (algebraMap F A) chart.x = 0

noncomputable def NormalizedAmbientIdealChart.transport
    {F A : Type u} [Field F] [CommRing A]
    {σ : Type} [Finite σ]
    (B₁ B₂ : Algebra F A) (hB : B₁ = B₂)
    (I : HomogeneousIdeal (homogeneousSubmodule σ F))
    (t : Spec (.of A) ⟶ Proj (homogeneousSubmodule σ F))
    (C : HomogeneousIdeal (homogeneousSubmodule σ F))
    (T : @NormalizedAmbientIdealChart F A _ _ B₁ σ _ I t C) :
    @NormalizedAmbientIdealChart F A _ _ B₂ σ _ I t C := by
  subst B₂
  exact T

/-- The packaged chart transports without expanding any of its dependent
fields in the calling theorem. -/
noncomputable def NormalizedAmbientChart.transport
    {F A : Type u} [Field F] [CommRing A]
    {σ : Type} [Finite σ]
    (B₁ B₂ : Algebra F A) (hB : B₁ = B₂)
    (I : HomogeneousIdeal (homogeneousSubmodule σ F))
    (t : Spec (.of A) ⟶ Proj (homogeneousSubmodule σ F))
    (T : @NormalizedAmbientChart F A _ _ B₁ σ _ I t) :
    @NormalizedAmbientChart F A _ _ B₂ σ _ I t := by
  subst B₂
  exact T

/-- Transport all data of a normalized ambient chart across equality of
coefficient-algebra structures in one step. -/
theorem exists_linearNormalizedPointAt_algebra_transport
    {F A : Type u} [Field F] [CommRing A]
    {σ : Type} [Finite σ]
    (B₁ B₂ : Algebra F A) (hB : B₁ = B₂)
    (I : HomogeneousIdeal (homogeneousSubmodule σ F))
    (x : σ → A)
    (he₁ : ∀ q ∈ I.toIdeal, q.eval₂ (@algebraMap F A _ _ B₁) x = 0)
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (hOne₁ : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (@algebraMap F A _ _ B₁) x) he₁) z = 1) :
    ∃ (he₂ : ∀ q ∈ I.toIdeal,
        q.eval₂ (@algebraMap F A _ _ B₂) x = 0)
      (hOne₂ : (Ideal.Quotient.lift I.toIdeal
        (eval₂Hom (@algebraMap F A _ _ B₂) x) he₂) z = 1),
      @linearNormalizedPointAt F A _ _ B₁ σ I x he₁ z hz hOne₁ =
        @linearNormalizedPointAt F A _ _ B₂ σ I x he₂ z hz hOne₂ := by
  subst B₂
  exact ⟨he₁, hOne₁, rfl⟩

end PfaffianDescent
