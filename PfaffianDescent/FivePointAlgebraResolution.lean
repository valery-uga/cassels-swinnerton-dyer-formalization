import PfaffianDescent.QuinticAlgebraCoordinateResolution
import PfaffianDescent.FivePointAlgebraPresentation
import PfaffianDescent.AlgebraVectorCoordinateChange
import PfaffianDescent.FiveQuadricResolutionEquiv
import PfaffianDescent.HomogeneousCoordinateEquiv

namespace PfaffianDescent
open MvPolynomial Module
section
variable {K A L : Type*} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]

/-- The canonical finite-algebra resolution, bundled with its homogeneous degrees
and alternating structure. -/
theorem exists_power_basis_five_quadric_resolution (z : A) (b : Basis (Fin 5) K A)
    (hb : ∀ i, b i = z^(i : ℕ)) (ev : Fin 5 → A →ₐ[K] L) (hev : Function.Injective ev) :
    Nonempty (FiveQuadricResolution K (algebraVectorIdeal (K := K) (rationalCubicCoordinates z))) := by
  obtain ⟨r, _, _, he1, he2, hI⟩ := quintic_algebra_coordinate_free_resolution z b hb ev hev
  exact ⟨{
    quadrics := quinticRelations r
    matrix := quinticPolynomialMatrix r
    quadrics_independent := quinticRelations_independent r
    quadrics_homogeneous := quinticRelations_homogeneous r
    matrix_homogeneous := quinticPolynomialMatrix_homogeneous r
    matrix_alternating := quinticSyzygyMatrix_alternating (fun i => C (r i)) X
    first_exact := he1
    last_exact := he2
    image_eq := hI }⟩

/-- The full minimal self-dual resolution over the ground field for arbitrary
finite-algebra coordinates whose five geometric points are in general position.
No normal form, resolution, or descent hypothesis is assumed. -/
theorem five_point_algebra_free_resolution [Infinite K] [FiniteDimensional K A]
    (hdim : finrank K A = 5) (ev : Fin 5 → A →ₐ[K] L) (hev : Function.Injective ev)
    (p : Vec A 4) (hgp : FivePointGeneralPosition (fun i j => ev i (p j))) :
    Nonempty (FiveQuadricResolution K (algebraVectorIdeal (K := K) p)) := by
  obtain ⟨z, b, hb⟩ := exists_power_basis_of_distinct_homs hdim ev hev
  obtain ⟨ell, hell, hspan⟩ := geometric_frame_has_frobenius_hyperplane hdim ev hev p hgp
  obtain ⟨u, M, hinj, hp⟩ := independent_quintic_algebra_coordinates z b hb p
    (coordinates_independent_of_geometric_frame ev p hgp) ell hell hspan
  have hM : IsUnit M.det := M.isUnit_iff_isUnit_det.mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  obtain ⟨S⟩ := exists_power_basis_five_quadric_resolution z b hb ev hev
  let E := (linearSubstitutionEquiv M hM).symm
  have hE : ∀ d (f : MvPolynomial (Fin 4) K), f.IsHomogeneous d → (E f).IsHomogeneous d :=
    homogeneous_equiv_symm (linearSubstitutionEquiv M hM)
      (fun _ _ hf => linearSubstitution_homogeneous M hf)
  have hI : (algebraVectorIdeal (K := K) (rationalCubicCoordinates z)).map E.toRingHom =
      algebraVectorIdeal (K := K) p := by
    rw [hp]
    exact algebraVectorIdeal_coordinate_normalization u M hM (rationalCubicCoordinates z)
  rw [← hI]
  exact ⟨S.map E hE⟩

end
end PfaffianDescent
