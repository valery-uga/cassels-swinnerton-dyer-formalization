import PfaffianDescent.QuinticHomogeneousGorenstein
import PfaffianDescent.FivePointAlgebraPresentation
import PfaffianDescent.AlgebraVectorCoordinateChange

namespace PfaffianDescent
open CategoryTheory MvPolynomial Module
universe u
section
variable {K A L : Type u} [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L] [FiniteDimensional K A]

/-- The homogeneous coordinate ring of every reduced length-five algebraic
projective frame is Noetherian and has self-injective dimension at most one over
the original field. The Frobenius form, coordinate normalization, and Gorenstein
descent are all constructed in the proof. -/
theorem five_point_algebra_homogeneous_gorenstein
    (hdim : finrank K A = 5) (ev : Fin 5 → A →ₐ[K] L) (hev : Function.Injective ev)
    (p : Vec A 4) (hgp : FivePointGeneralPosition (fun i j => ev i (p j))) :
    IsNoetherianRing (MvPolynomial (Fin 4) K ⧸ algebraVectorIdeal (K := K) p) ∧
      HasInjectiveDimensionLE
        (ModuleCat.of (MvPolynomial (Fin 4) K ⧸ algebraVectorIdeal (K := K) p)
          (MvPolynomial (Fin 4) K ⧸ algebraVectorIdeal (K := K) p)) 1 := by
  obtain ⟨z, b, hb⟩ := exists_power_basis_of_distinct_homs hdim ev hev
  obtain ⟨ell, hell, hspan⟩ := geometric_frame_has_frobenius_hyperplane hdim ev hev p hgp
  obtain ⟨u, M, hinj, hp⟩ := independent_quintic_algebra_coordinates z b hb p
    (coordinates_independent_of_geometric_frame ev p hgp) ell hell hspan
  have hM : IsUnit M.det := M.isUnit_iff_isUnit_det.mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  let E := (linearSubstitutionEquiv M hM).symm
  have hI : (algebraVectorIdeal (K := K) (rationalCubicCoordinates z)).map E.toRingHom =
      algebraVectorIdeal (K := K) p := by
    rw [hp]
    exact algebraVectorIdeal_coordinate_normalization u M hM (rationalCubicCoordinates z)
  let e : (MvPolynomial (Fin 4) K ⧸ algebraVectorIdeal (K := K) (rationalCubicCoordinates z)) ≃ₐ[K]
      (MvPolynomial (Fin 4) K ⧸ algebraVectorIdeal (K := K) p) :=
    Ideal.quotientEquivAlg _ _ E hI.symm
  exact ⟨inferInstance, (self_injectiveDimensionLE_ringEquiv e.toRingEquiv 1).mp
    (power_basis_homogeneous_gorenstein z b hb ev hev)⟩

end
end PfaffianDescent
