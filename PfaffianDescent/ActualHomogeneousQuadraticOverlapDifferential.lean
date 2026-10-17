import PfaffianDescent.ActualHomogeneousQuadraticOverlapFraction
import PfaffianDescent.ActualResidueDifferentialLeibnizBalance

/- SOURCE ONLY / UNVERIFIED. In the ACTUAL homogeneous overlap ring, the
zero-section differential transforms by the square coordinate ratio. The
residue-zero condition is ordinary local vanishing; original H0 caller
must derive it from its exact scheme restriction, not assume Phi equality. -/
noncomputable section
namespace PfaffianDescent
open HomogeneousLocalization TensorProduct
open AllCharacteristics.GradedChart
open scoped TensorProduct
universe u
variable {K A L : Type u} [Field K] [CommRing A] [Algebra K A] [Field L]
  [Algebra K L] (G : ℕ → Submodule K A) [GradedRing G]
  {f g : A} (hf : f ∈ G 1) (hg : g ∈ G 1)

lemma actualHomogeneousQuadratic_overlap_residueDifferential
    (rho : Away G (f * g) →+* L)
    (hbase : rho.comp (baseMap G (z := f * g)) = algebraMap K L)
    (Q : A) (hQ : Q ∈ G 2)
    (hzero : rho (awayMap G hf (mul_comm f g) (Away.mk G hg 2 Q hQ)) = 0) :
    let B := Away G (f * g)
    letI : Algebra K B := (baseMap G (z := f * g)).toAlgebra
    letI : Algebra B L := rho.toAlgebra
    letI : IsScalarTower K B L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun hbase c).symm)
    actualResidueDifferentialDerivation (K := K) (R := B) (L := L)
      (awayMap G hg rfl (Away.mk G hf 2 Q hQ)) =
      rho (awayMap G hg rfl (normalized G hf g hg)) ^ 2 •
        actualResidueDifferentialDerivation (K := K) (R := B) (L := L)
          (awayMap G hf (mul_comm f g) (Away.mk G hg 2 Q hQ)) := by
  dsimp only
  let B := Away G (f * g)
  letI : Algebra K B := (baseMap G (z := f * g)).toAlgebra
  letI : Algebra B L := rho.toAlgebra
  letI : IsScalarTower K B L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun hbase c).symm)
  rw [quadratic_normalized_overlap_mul]
  simpa only [map_pow] using actualResidueDifferential_zero_section_leibniz
    ((awayMap G hg rfl (normalized G hf g hg)) ^ 2)
    (awayMap G hf (mul_comm f g) (Away.mk G hg 2 Q hQ)) hzero

end PfaffianDescent
