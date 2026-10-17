import PfaffianDescent.ProjectiveIdealSaturation
import AllCharacteristics.HomogeneousProjectiveAmbient

/-! Scheme-theoretic homogeneous vanishing in every degree.  Unlike a
carrier vanishing ideal, this uses the actual ideal sheaf kernel and retains
nilpotents.  The absence of an irrelevant socle removes localization torsion. -/

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem homogeneous_mem_of_hypersurface_ker_le_of_no_irrelevant_annihilator
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d)
    (hker : (hypersurfaceToAmbient p hp).ker ≤ (quotientProjMap I).ker)
    (hsocle : ∀ x : CoordinateRing I,
      (∀ j : Fin 4, coordinate I j * x = 0) → x = 0) :
    p ∈ I.toIdeal := by
  apply mem_of_coordinate_localization_eq_zero_of_no_irrelevant_annihilator
    I.toIdeal (X 0) (X 1) (X 2) (X 3) p
  · intro x hx0 hx1 hx2 hx3
    apply hsocle x
    intro j
    fin_cases j
    · exact hx0
    · exact hx1
    · exact hx2
    · exact hx3
  · have hzero (j : Fin 4) :
        algebraMap (CoordinateRing I)
          (Localization (Submonoid.powers (coordinate I j)))
          (Ideal.Quotient.mk I.toIdeal p) = 0 := by
      apply localization_eq_zero_of_away_mk_eq_zero
        (grading I) (coordinate_mem I j) d
      · exact away_mk_eq_zero_of_hypersurface_ker_le_quotientProjMap_coordinate
          p hp I hker j
      · simpa using polynomial_class_mem_grading I p hp
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hzero 0
    · exact hzero 1
    · exact hzero 2
    · exact hzero 3

end PfaffianDescent
