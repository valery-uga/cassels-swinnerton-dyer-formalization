import PfaffianDescent.GeometricFrobenius
import PfaffianDescent.SeparatingElement
import PfaffianDescent.AlgebraPointPresentation

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable {K A L : Type*} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L] [FiniteDimensional K A]

/-- Geometric general position implies independence of the four coordinate functions
already over the ground field. -/
theorem coordinates_independent_of_geometric_frame (ev : Fin 5 → A →ₐ[K] L) (p : Vec A 4)
    (hgp : FivePointGeneralPosition (fun i j => ev i (p j))) : LinearIndependent K p := by
  let M : Mat L 4 := fun i j => ev i.castSucc (p j)
  have hrows : LinearIndependent L M := hgp Fin.castSucc (Fin.castSucc_injective 4)
  have hcols := (Matrix.Nonsingular.of_linearIndependent_row hrows).linearIndependent_col
  let E : A →ₗ[K] Vec L 4 := LinearMap.pi (fun i : Fin 4 => (ev i.castSucc).toLinearMap)
  apply LinearIndependent.of_comp E
  exact hcols.restrict_scalars' K

private theorem algebra_hyperplane_eq_kernel (W : Submodule K A)
    (hW : finrank K W + 1 = finrank K A) :
    ∃ ell : Module.Dual K A, ell ≠ 0 ∧ W = LinearMap.ker ell := by
  have hproper : W < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro h
    rw [h, finrank_top] at hW
    omega
  obtain ⟨ell, hell, hmap⟩ := W.exists_dual_map_eq_bot_of_lt_top hproper inferInstance
  refine ⟨ell, hell, ?_⟩
  have hle : W ≤ LinearMap.ker ell := by
    intro x hx
    have hm : ell x ∈ W.map ell := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hmap, Submodule.mem_bot] at hm
    exact hm
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hell
  omega

/-- The coordinate hyperplane and its nondegenerate multiplication functional are
consequences of the geometric hypotheses, rather than additional presentation inputs. -/
theorem geometric_frame_has_frobenius_hyperplane (hdim : finrank K A = 5)
    (ev : Fin 5 → A →ₐ[K] L) (hev : Function.Injective ev) (p : Vec A 4)
    (hgp : FivePointGeneralPosition (fun i j => ev i (p j))) :
    ∃ ell : Module.Dual K A, IsFrobeniusFunctional ell ∧
      Submodule.span K (Set.range p) = LinearMap.ker ell := by
  have hp := coordinates_independent_of_geometric_frame ev p hgp
  let W := Submodule.span K (Set.range p)
  have hW : finrank K W = 4 := by simpa using finrank_span_eq_card hp
  obtain ⟨ell, hell, hker⟩ := algebra_hyperplane_eq_kernel W (by omega)
  refine ⟨ell, frobenius_of_five_point_general_position hdim ev hev p hgp ell hell ?_, hker⟩
  intro j
  have hpj : p j ∈ W := Submodule.subset_span (Set.mem_range_self j)
  rw [hker] at hpj
  exact hpj

end

section
variable {K A L : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L] [FiniteDimensional K A]

/-- The five-point Pfaffian presentation for a length-five algebra with five distinct
geometric points in general linear position. No power basis, Frobenius functional,
or field-of-definition descent is assumed: all are constructed over `K`. -/
theorem five_point_algebra_polynomial_presentation (hdim : finrank K A = 5)
    (ev : Fin 5 → A →ₐ[K] L) (hev : Function.Injective ev) (p : Vec A 4)
    (hgp : FivePointGeneralPosition (fun i j => ev i (p j)))
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (hF : MvPolynomial.eval₂ (algebraMap K A) p f = 0) :
    ∃ P : Fin 4 → Mat K 6, (∀ i, IsAlternating (P i)) ∧ (pfaffianCubic P).toMvPolynomial = f := by
  obtain ⟨a, b, hb⟩ := exists_power_basis_of_distinct_homs hdim ev hev
  obtain ⟨ell, hell, hspan⟩ := geometric_frame_has_frobenius_hyperplane hdim ev hev p hgp
  exact quintic_algebra_polynomial_presentation a b hb p
    (coordinates_independent_of_geometric_frame ev p hgp) ell hell hspan f hf hF

end
end PfaffianDescent
