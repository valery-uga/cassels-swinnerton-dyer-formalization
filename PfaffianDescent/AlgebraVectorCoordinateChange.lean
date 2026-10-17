import PfaffianDescent.AlgebraLineScaling

namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators
section
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

lemma algebraLineHom_linearCoordinate (M : Mat K 4) (p : Vec A 4) (i : Fin 4) :
    algebraLineHom (K := K) p (linearCoordinate M i) =
      C ((M.map (algebraMap K A)).mulVec p i) * X () := by
  change algebraLineHom p (∑ j, C (M i j) * X j) =
    C (∑ j, algebraMap K A (M i j) * p j) * X ()
  simp only [map_sum, map_mul, algebraLineHom_C, algebraLineHom_X]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma algebraLineHom_linearSubstitution (M : Mat K 4) (p : Vec A 4) :
    (algebraLineHom (K := K) p).comp (linearSubstitution M) =
      algebraLineHom (K := K) ((M.map (algebraMap K A)).mulVec p) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, linearSubstitution_X, algebraLineHom_linearCoordinate, algebraLineHom_X]

lemma algebraVectorIdeal_linearSubstitution (M : Mat K 4) (p : Vec A 4) :
    algebraVectorIdeal (K := K) ((M.map (algebraMap K A)).mulVec p) =
      (algebraVectorIdeal (K := K) p).comap (linearSubstitution M).toRingHom := by
  ext f
  change algebraLineHom ((M.map (algebraMap K A)).mulVec p) f = 0 ↔
    algebraLineHom p (linearSubstitution M f) = 0
  rw [← AlgHom.congr_fun (algebraLineHom_linearSubstitution M p) f]
  rfl

/-- A ground-field matrix and a common algebra unit transform the homogeneous
ideal by the inverse polynomial coordinate substitution. -/
theorem algebraVectorIdeal_coordinate_normalization (u : Aˣ) (M : Mat K 4)
    (hM : IsUnit M.det) (p : Vec A 4) :
    (algebraVectorIdeal (K := K) p).map (linearSubstitutionEquiv M hM).symm.toRingHom =
      algebraVectorIdeal (K := K) ((u : A) • (M.map (algebraMap K A)).mulVec p) := by
  rw [algebraVectorIdeal_unit_smul]
  calc
    _ = (algebraVectorIdeal (K := K) p).comap (linearSubstitution M).toRingHom :=
      Ideal.map_comap_of_equiv (linearSubstitutionEquiv M hM).symm.toRingEquiv
    _ = algebraVectorIdeal (K := K) ((M.map (algebraMap K A)).mulVec p) :=
      (algebraVectorIdeal_linearSubstitution M p).symm

end
end PfaffianDescent
