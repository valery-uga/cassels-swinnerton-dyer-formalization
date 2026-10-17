import PfaffianDescent.ActualHomogeneousQuadraticOverlapFraction
import PfaffianDescent.ActualRelativeDifferentialSectionLeibniz

/- SOURCE ONLY / UNVERIFIED. Literal structure-sheaf quadratic overlap
identity and its derivative in genuine global Omega on the SAME Proj.
Native restrictions identify with these actual sections by the existing
Proj.awayMap_awayToSection theorem, not an assumed comparison certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open AllCharacteristics.GradedChart
universe u
variable {K A : Type u} [CommRing K] [CommRing A] [Algebra K A]
  (G : ℕ → Submodule K A) [GradedRing G]
  {f g : A} (hf : f ∈ G 1) (hg : g ∈ G 1)

def actualHomogeneousQuadraticProductOpenSection
    (Q : A) (hQ : Q ∈ G 2) : Γ(Proj G, Proj.basicOpen G (f * g)) :=
  (Proj.awayToSection G (f * g)).hom (awayMap G hg rfl (Away.mk G hf 2 Q hQ))

lemma actualHomogeneousQuadratic_productOpenSection_transition
    (Q : A) (hQ : Q ∈ G 2) :
    actualHomogeneousQuadraticProductOpenSection G hf hg Q hQ =
      ((Proj.awayToSection G (f * g)).hom
        (awayMap G hg rfl (normalized G hf g hg))) ^ 2 *
      (Proj.awayToSection G (f * g)).hom
        (awayMap G hf (mul_comm f g) (Away.mk G hg 2 Q hQ)) := by
  unfold actualHomogeneousQuadraticProductOpenSection
  rw [quadratic_normalized_overlap_mul, map_mul, map_pow]

lemma actualHomogeneousQuadratic_productOpenSection_D_transition
    (gBase : Proj G ⟶ Spec (.of K)) (Q : A) (hQ : Q ∈ G 2) :
    let W := Proj.basicOpen G (f * g)
    let ratio := (Proj.awayToSection G (f * g)).hom
      (awayMap G hg rfl (normalized G hf g hg))
    let qg := (Proj.awayToSection G (f * g)).hom
      (awayMap G hf (mul_comm f g) (Away.mk G hg 2 Q hQ))
    actualRelativeDifferentialSection gBase W
      (actualHomogeneousQuadraticProductOpenSection G hf hg Q hQ) =
      ratio ^ 2 • actualRelativeDifferentialSection gBase W qg +
        qg • actualRelativeDifferentialSection gBase W (ratio ^ 2) := by
  dsimp only
  rw [actualHomogeneousQuadratic_productOpenSection_transition,
    actualRelativeDifferentialSection_leibniz]

end PfaffianDescent
