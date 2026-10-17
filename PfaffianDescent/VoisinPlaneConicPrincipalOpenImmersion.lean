import PfaffianDescent.VoisinConicPrincipalOpenAlgebra

/-!
# The plane conic as a Cartier divisor on a cubic

The actual plane-conic closed immersion is presented on principal-open
refinements of every standard cubic chart. The only remaining geometric
premise is that the cubic's partial derivatives generate the unit ideal
on those charts. This premise is known to imply smoothness; the converse
from abstract scheme smoothness is kept separate.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The range of a four-entry vector is exactly its four displayed entries. -/
private theorem range_fourVector {A : Type u} (x₀ x₁ x₂ x₃ : A) :
    Set.range (![x₀, x₁, x₂, x₃] : Fin 4 → A) =
      ({x₀, x₁, x₂, x₃} : Set A) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

/-- A smooth nonzero cubic with a chartwise Jacobian certificate contains
its plane conic as an actual regular-principal closed immersion. The plane
equation must be nonzero; the four natural functions `ell,q,a,b` then
provide the requisite principal-open refinements. -/
noncomputable def planeConicToCubic_regularPrincipalImmersion_of_chartJacobian_top
    (p ell q a b : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0)
    (hq : q.IsHomogeneous 2)
    (h : p = ell * a + q * b)
    (hjac : ∀ j : Fin 4,
      let I := equationIdeal p hp
      Ideal.span (Set.range (fun i : Fin 4 =>
        (pderiv i p).eval₂ (chartBaseMap I j) (chartCoordinate I j))) = ⊤) :
    RegularPrincipalImmersion
      (planeConicToCubic p ell q hp hell hq
        (cubic_mem_planeConicIdeal_of_decomposition p ell q a b h)) := by
  let hpc := cubic_mem_planeConicIdeal_of_decomposition p ell q a b h
  let I := equationIdeal p hp
  let J := planeConicHomogeneousIdeal ell q hell hq
  let hIJ := equationIdeal_le_planeConicHomogeneousIdeal
    p ell q hp hell hq hpc
  let e (j : Fin 4) := eval₂Hom (chartBaseMap I j) (chartCoordinate I j)
  let s : ∀ j : Fin 4, Fin 4 → ChartRing I j :=
    fun j => ![e j ell, e j q, e j a, e j b]
  have hcover : ∀ j, Ideal.span (Set.range (s j)) = ⊤ := by
    intro j
    change Ideal.span (Set.range
      (![e j ell, e j q, e j a, e j b] : Fin 4 → ChartRing I j)) = ⊤
    rw [range_fourVector]
    apply planeConic_coefficientIdeal_top_of_jacobian_top
      p ell q a b h (e j)
    simpa only [e, I, MvPolynomial.coe_eval₂Hom] using hjac j
  have hprincipal : ∀ (j : Fin 4) (k : Fin 4),
      let g := chartQuotientMap I J hIJ j
      ∃ z : Localization.Away (s j k),
        IsRegular z ∧
          RingHom.ker (Localization.awayMap g (s j k)) =
            Ideal.span ({z} : Set (Localization.Away (s j k))) := by
    intro j k
    letI : IsDomain (ChartRing I j) :=
      smoothCubic_chartRing_isDomain p hp hp0 j
    have hmem : s j k ∈
        ({e j ell, e j q, e j a, e j b} : Set (ChartRing I j)) := by
      rw [← range_fourVector]
      exact ⟨k, rfl⟩
    exact conicPrincipalOpen_localizedKernel_regularPrincipal_of_mem
      (chartQuotientMap I J hIJ j)
      (e j ell) (e j q) (e j a) (e j b)
      (planeConicToCubic_chartKernel_eq_span_pair
        p ell q hp hell hq hpc j)
      (planeConic_cubicChart_relation p ell q a b hp h j)
      (smoothCubic_chartEval_ne_zero_of_degree_lt_three
        p hp hp0 ell 1 hell hell0 (by omega) j)
      (s j k) hmem
  exact regularPrincipalImmersion_of_principalOpenCharts
    I J hIJ (fun _ : Fin 4 => Fin 4) s hcover hprincipal

end PfaffianDescent
