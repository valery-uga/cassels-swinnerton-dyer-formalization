import PfaffianDescent.PolynomialQuotientGorensteinDescent
import PfaffianDescent.FivePointHomogeneousGorenstein
import PfaffianDescent.QuinticAlgebraCoordinateResolution

namespace PfaffianDescent
open CategoryTheory MvPolynomial Module
universe u
section
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

lemma quinticIdeal_baseChange (a : Vec K 5) :
    (quinticIdeal a).map (MvPolynomial.map (algebraMap K L)) =
      quinticIdeal (fun i => algebraMap K L (a i)) := by
  simp only [quinticIdeal, Ideal.map_span, ← Set.range_comp, Function.comp_def,
    quinticRelations_baseChange]

/-- The homogeneous quintic coordinate ring is Gorenstein over the ground field
whenever its five geometric points form a projective frame. -/
theorem quintic_geometric_homogeneous_gorenstein [CharZero K] (a : Vec K 5)
    (p : Fin 5 → (Fin 4 → L)) (hp : FivePointGeneralPosition p)
    (hq : ∀ i, MvPolynomial.map (algebraMap K L) (quinticRelations a i) ∈ fiveVectorIdeal p) :
    HasInjectiveDimensionLE
      (ModuleCat.of (MvPolynomial (Fin 4) K ⧸ quinticIdeal a)
        (MvPolynomial (Fin 4) K ⧸ quinticIdeal a)) 1 := by
  letI : CharZero L := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective K L)
  have hqL (i : Fin 5) : quinticRelations (fun j => algebraMap K L (a j)) i ∈ fiveVectorIdeal p := by
    rw [← quinticRelations_baseChange]
    exact hq i
  have hI : (quinticIdeal a).map (MvPolynomial.map (algebraMap K L)) = fiveVectorIdeal p :=
    (quinticIdeal_baseChange a).trans ((quinticLastMap_range _).symm.trans
      (quintic_frame_free_resolution _ p hp hqL).2.2.2)
  letI : HasInjectiveDimensionLE
      (ModuleCat.of (MvPolynomial (Fin 4) L ⧸ (quinticIdeal a).map (MvPolynomial.map (algebraMap K L)))
        (MvPolynomial (Fin 4) L ⧸ (quinticIdeal a).map (MvPolynomial.map (algebraMap K L)))) 1 := by
    rw [hI]
    exact (five_point_homogeneous_ring_gorenstein p hp).2
  exact polynomial_quotient_self_injectiveDimensionLE_descent (L := L) (quinticIdeal a) 1

variable {A : Type u} [CommRing A] [Algebra K A]

/-- The actual homogeneous coordinate ring of the canonical power-basis five-point
scheme has finite self-injective dimension over its original coefficient field. -/
theorem power_basis_homogeneous_gorenstein [CharZero K]
    (z : A) (b : Basis (Fin 5) K A) (hb : ∀ i, b i = z^(i : ℕ))
    (ev : Fin 5 → A →ₐ[K] L) (hev : Function.Injective ev) :
    HasInjectiveDimensionLE
      (ModuleCat.of (MvPolynomial (Fin 4) K ⧸ algebraVectorIdeal (K := K) (rationalCubicCoordinates z))
        (MvPolynomial (Fin 4) K ⧸ algebraVectorIdeal (K := K) (rationalCubicCoordinates z))) 1 := by
  obtain ⟨a, ha, _, _, _, hI⟩ := quintic_algebra_coordinate_free_resolution z b hb ev hev
  have hIa : quinticIdeal a = algebraVectorIdeal (K := K) (rationalCubicCoordinates z) :=
    (quinticLastMap_range a).symm.trans hI
  rw [← hIa]
  apply quintic_geometric_homogeneous_gorenstein a (fun i => rationalCubicCoordinates (ev i z))
    (rationalCubicCoordinates_general_position _ (power_basis_separates_homs z b hb ev hev))
  intro i
  rw [quinticRelations_baseChange, fiveVectorIdeal, Submodule.mem_iInf]
  intro j
  exact quinticRelations_mem_point _ _
    (quinticQuadrics_at_root _ _ (quinticRelation_algHom a z ha (ev j))) i

end
end PfaffianDescent
