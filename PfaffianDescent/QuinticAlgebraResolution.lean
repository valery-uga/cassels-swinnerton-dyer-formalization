import PfaffianDescent.QuinticRootFrame
import PfaffianDescent.AlgebraQuinticPresentation
import PfaffianDescent.SeparatingElement

namespace PfaffianDescent
open MvPolynomial Module
section
variable {K A L : Type*} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]

/-- Distinct geometric evaluations have distinct values on a power-basis generator. -/
theorem power_basis_separates_homs (z : A) (b : Basis (Fin 5) K A)
    (hb : ∀ i, b i = z^(i : ℕ)) (ev : Fin 5 → A →ₐ[K] L) (hev : Function.Injective ev) :
    Function.Injective (fun i => ev i z) := by
  intro i j hij
  change ev i z = ev j z at hij
  apply hev
  have he : (ev i).toLinearMap = (ev j).toLinearMap := by
    apply b.ext
    intro k
    change ev i (b k) = ev j (b k)
    rw [hb, map_pow, map_pow, hij]
  ext x
  exact LinearMap.congr_fun he x

lemma quinticRelation_algHom (r : Vec K 5) (z : A)
    (hr : quinticRelation (fun i => algebraMap K A (r i)) z) (f : A →ₐ[K] L) :
    quinticRelation (fun i => algebraMap K L (r i)) (f z) := by
  unfold quinticRelation at hr ⊢
  have h := congrArg f hr
  simpa only [map_add, map_mul, map_pow, AlgHom.commutes, map_zero] using h

/-- A power-basis presentation of a reduced length-five algebra yields the
full explicit polynomial resolution over the original coefficient field.
All geometric hypotheses of the resolution are proved from the evaluations. -/
theorem quintic_algebra_power_free_resolution (z : A) (b : Basis (Fin 5) K A)
    (hb : ∀ i, b i = z^(i : ℕ)) (ev : Fin 5 → A →ₐ[K] L) (hev : Function.Injective ev) :
    ∃ r : Vec K 5, quinticRelation (fun i => algebraMap K A (r i)) z ∧
      Function.Injective (quinticFirstMap r) ∧
      LinearMap.range (quinticFirstMap r) = LinearMap.ker (quinticMiddleMap r) ∧
      LinearMap.range (quinticMiddleMap r) = LinearMap.ker (quinticLastMap r) ∧
      LinearMap.range (quinticLastMap r) =
        (fiveVectorIdeal (fun i => rationalCubicCoordinates (ev i z))).comap
          (MvPolynomial.map (algebraMap K L)) := by
  obtain ⟨r, hr⟩ := quintic_root_of_algebra_power_basis z b hb
  refine ⟨r, hr, ?_⟩
  apply quintic_geometric_free_resolution r _
    (rationalCubicCoordinates_general_position _ (power_basis_separates_homs z b hb ev hev))
  intro i
  rw [quinticRelations_baseChange]
  rw [fiveVectorIdeal, Submodule.mem_iInf]
  intro j
  exact quinticRelations_mem_point _ _
    (quinticQuadrics_at_root _ _ (quinticRelation_algHom r z hr (ev j))) i

end
end PfaffianDescent
