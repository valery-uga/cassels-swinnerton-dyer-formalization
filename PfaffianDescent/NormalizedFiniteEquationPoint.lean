import PfaffianDescent.NormalizedProjectiveQuotientFactor

/-! Actual normalized points in homogeneous equation schemes. The coefficient
map, closed immersion, and ambient map are retained without any assumption
on the quadratic base locus or complete intersection. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- A normalized coordinate map into any homogeneous scheme whose equations
vanish in the actual coordinate algebra. -/
def normalizedFiniteEquationPoint
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → A) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hellOne : ell.eval₂ (algebraMap K A) x = 1)
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0) :
    Spec (.of A) ⟶ scheme I :=
  linearNormalizedPointAt I x he (Ideal.Quotient.mk I.toIdeal ell)
    (polynomial_class_mem_grading I ell hell) (by
      change ell.eval₂ (algebraMap K A) x = 1
      exact hellOne)

theorem normalizedFiniteEquationPoint_toBase
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → A) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hellOne : ell.eval₂ (algebraMap K A) x = 1)
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0) :
    normalizedFiniteEquationPoint I x ell hell hellOne he ≫ toBase I =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) :=
  linearNormalizedPointAt_toBase I x he _ _ _

theorem normalizedFiniteEquationPoint_isClosedImmersion [Module.Finite K A]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → A) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hellOne : ell.eval₂ (algebraMap K A) x = 1)
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0)
    (hgen : Function.Surjective (eval₂Hom (algebraMap K A) x)) :
    IsClosedImmersion (normalizedFiniteEquationPoint I x ell hell hellOne he) :=
  linearNormalizedPointAt_isClosedImmersion I x he _ _ _ hgen

/-- All equation maps reconstruct exactly the same ambient projective map. -/
theorem normalizedFiniteEquationPoint_toAmbient
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → A) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hellOne : ell.eval₂ (algebraMap K A) x = 1)
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0) :
    normalizedFiniteEquationPoint I x ell hell hellOne he ≫ quotientProjMap I =
      normalizedFiniteEquationPoint ⊥ x ell hell hellOne
        (fun p hp => by simp [show p = 0 from Ideal.mem_bot.mp hp]) ≫
          quotientProjMap ⊥ := by
  let I₀ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) := ⊥
  have he₀ : ∀ p ∈ I₀.toIdeal, p.eval₂ (algebraMap K A) x = 0 := by
    intro p hp
    have hp0 : p = 0 := Ideal.mem_bot.mp hp
    simp [hp0]
  have hfac := linearNormalizedPointAt_comp_schemeQuotientMap I₀ I bot_le
    x he₀ he (Ideal.Quotient.mk I₀.toIdeal ell)
    (polynomial_class_mem_grading I₀ ell hell)
    (by change ell.eval₂ (algebraMap K A) x = 1; exact hellOne)
    (by change ell.eval₂ (algebraMap K A) x = 1; exact hellOne)
  have hfac' : normalizedFiniteEquationPoint I x ell hell hellOne he ≫
      schemeQuotientMap I₀ I bot_le =
      normalizedFiniteEquationPoint I₀ x ell hell hellOne he₀ := by
    have hclass : gradedQuotientMap I₀ I bot_le (Ideal.Quotient.mk I₀.toIdeal ell) =
        Ideal.Quotient.mk I.toIdeal ell := rfl
    simpa only [normalizedFiniteEquationPoint, hclass] using hfac
  rw [← schemeQuotientMap_comp_quotientProjMap I₀ I bot_le,
    ← Category.assoc, hfac']

end PfaffianDescent
