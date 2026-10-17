import PfaffianDescent.HomogeneousCoordinateEquiv
import PfaffianDescent.PolynomialLinearChange
import PfaffianDescent.ProjectiveFiniteOfHilbertBound
import PfaffianDescent.ProjectiveLengthOfHilbert

/-!
# Projective finite rank under linear coordinate changes

An invertible linear substitution identifies the homogeneous quotient pieces
of ideals carried into one another.  Eventual Hilbert dimensions therefore
give finiteness and finite scheme rank without constructing a separate Proj
automorphism.
-/

namespace PfaffianDescent

open MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K]

noncomputable def linearCoordinateChangeGradeMap
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom)
    (n : ℕ) :
    grading I n →ₗ[K] grading J n :=
  ((Ideal.quotientEquivAlg I.toIdeal J.toIdeal (linearSubstitutionEquiv M hM) hIJ).toLinearMap.domRestrict _).codRestrict _ (fun x => by
      obtain ⟨p, hp, hpx⟩ := x.property
      change Ideal.quotientEquivAlg I.toIdeal J.toIdeal
        (linearSubstitutionEquiv M hM) hIJ x.val ∈ grading J n
      rw [← hpx]
      change Ideal.quotientEquivAlg I.toIdeal J.toIdeal
        (linearSubstitutionEquiv M hM) hIJ (Ideal.Quotient.mk I.toIdeal p) ∈ grading J n
      have hIJ' : J.toIdeal = I.toIdeal.map
          (↑(linearSubstitutionEquiv M hM) : MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) K) := by
        simpa using hIJ
      change Ideal.quotientEquivAlg I.toIdeal J.toIdeal
        (linearSubstitutionEquiv M hM) hIJ' (Ideal.Quotient.mk I.toIdeal p) ∈ grading J n
      rw [Ideal.quotientEquivAlg_mk]
      exact ⟨linearSubstitution M p, linearSubstitution_homogeneous M hp, rfl⟩)

theorem linearCoordinateChangeGradeMap_bijective
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom)
    (n : ℕ) :
    Function.Bijective (linearCoordinateChangeGradeMap M hM I J hIJ n) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply (Ideal.quotientEquivAlg I.toIdeal J.toIdeal (linearSubstitutionEquiv M hM) hIJ).injective
    exact congrArg Subtype.val hxy
  · intro y
    obtain ⟨p, hp, hpy⟩ := y.property
    let E := linearSubstitutionEquiv M hM
    have hp' : (E.symm p).IsHomogeneous n :=
      homogeneous_equiv_symm E (fun _ q hq => linearSubstitution_homogeneous M hq) n hp
    let x : grading I n := ⟨Ideal.Quotient.mk I.toIdeal (E.symm p),
      ⟨E.symm p, hp', rfl⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    rw [← hpy]
    change Ideal.quotientEquivAlg I.toIdeal J.toIdeal E hIJ
      (Ideal.Quotient.mk I.toIdeal (E.symm p)) = Ideal.Quotient.mk J.toIdeal p
    have hIJ' : J.toIdeal = I.toIdeal.map
        (↑E : MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) K) := by
      simpa [E] using hIJ
    change Ideal.quotientEquivAlg I.toIdeal J.toIdeal E hIJ'
      (Ideal.Quotient.mk I.toIdeal (E.symm p)) = Ideal.Quotient.mk J.toIdeal p
    rw [Ideal.quotientEquivAlg_mk, E.apply_symm_apply]

theorem linearCoordinateChange_grade_finrank
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom)
    (n : ℕ) :
    Module.finrank K (grading I n) = Module.finrank K (grading J n) := by
  let E := LinearEquiv.ofBijective (linearCoordinateChangeGradeMap M hM I J hIJ n)
    (linearCoordinateChangeGradeMap_bijective M hM I J hIJ n)
  exact E.finrank_eq

theorem projective_finite_of_linearCoordinateChange_hilbert_bound [Infinite K]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom)
    (N D : ℕ) (hI : ∀ n, N ≤ n → Module.finrank K (grading I n) ≤ D) :
    IsFinite (toBase J) := by
  apply projective_finite_of_hilbert_bound J N D
  intro n hn
  rw [← linearCoordinateChange_grade_finrank M hM I J hIJ n]
  exact hI n hn

theorem projective_length_of_linearCoordinateChange_eventual_hilbert [Infinite K]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom)
    (N D : ℕ) (hI : ∀ n, N ≤ n → Module.finrank K (grading I n) = D)
    [IsFinite (toBase J)] :
    AllCharacteristics.finiteSchemeRank (toBase J) = D := by
  apply projective_length_of_eventual_hilbert J N D
  intro n hn
  rw [← linearCoordinateChange_grade_finrank M hM I J hIJ n]
  exact hI n hn

theorem projective_finiteSchemeRank_of_linearCoordinateChange_eventual_hilbert [Infinite K]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom)
    (N D : ℕ) (hJ : ∀ n, N ≤ n → Module.finrank K (grading J n) = D) :
    ∃ hfinite : IsFinite (toBase I),
      @AllCharacteristics.finiteSchemeRank K _ _ (toBase I) hfinite = D := by
  have hI : ∀ n, N ≤ n → Module.finrank K (grading I n) = D := by
    intro n hn
    exact (linearCoordinateChange_grade_finrank M hM I J hIJ n).trans (hJ n hn)
  let hfinite : IsFinite (toBase I) := by
    apply projective_finite_of_hilbert_bound I N D
    intro n hn
    exact (hI n hn).le
  letI : IsFinite (toBase I) := hfinite
  exact ⟨hfinite, projective_length_of_eventual_hilbert I N D hI⟩

end PfaffianDescent
