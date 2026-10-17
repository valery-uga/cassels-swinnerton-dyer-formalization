import AllCharacteristics.HomogeneousClosedPoints
import PfaffianDescent.QuarticMultivariate

/-!
# Degree-four descent for actual projective cubic schemes

The coordinate degree-four theorem is applied to the actual residue fields of
an effective zero-cycle. Their dimensions equal the scheme residue degrees.
The resulting nonzero cubic zero is converted to a section of the hypersurface's
structure morphism. The characteristic-zero assumption is explicit.
-/

open AlgebraicGeometry CategoryTheory
open scoped BigOperators
namespace AllCharacteristics
namespace HomogeneousProjective
universe u

/-- An effective zero-cycle of degree four on an actual projective cubic
surface in characteristic zero gives a rational point. Smoothness is not needed. -/
theorem hypersurface_section_of_effective_degree_four
    {k : Type u} [Field k] [CharZero k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4) :
    ∃ q : Spec (.of k) ⟶ hypersurface p hp, q ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  classical
  let X := hypersurface p hp
  let f := hypersurfaceToBase p hp
  let ι := z.support
  let L : ι → Type u := fun x ↦ X.residueField x.1.1
  let : ∀ x : ι, Field (L x) := fun x ↦ inferInstance
  let : ∀ x : ι, Algebra k (L x) := fun x ↦ pointAlgebra f x.1.1
  have : ∀ x : ι, Module.Finite k (L x) := fun x ↦ closedPoint_moduleFinite f x.1
  have hc : ∀ x : ι, ∃ v : Fin 4 → L x, v ≠ 0 ∧
      p.eval₂ (algebraMap k (L x)) v = 0 :=
    fun x ↦ hypersurface_residueField_coordinates p hp x.1.1
  choose v hv he using hc
  have hd : ∑ x : ι, z x.1 * Module.finrank k (L x) = 4 :=
    (EffectiveZeroCycle.degree_eq_sum_finrank f z).symm.trans hz
  obtain ⟨y, hy, hey⟩ := PfaffianDescent.homogeneous_cubic_effective_degree_four_to_point
    L p hp (fun x ↦ z x.1) v (fun x _ ↦ hv x) (fun x _ ↦ he x) hd
  obtain ⟨q, hq⟩ := hypersurface_point_of_coordinates (RingHom.id k) p hp y hy hey
  exact ⟨q, by simpa using hq⟩

/-- A degree-four closed point on an actual projective cubic surface in
characteristic zero gives a rational point. -/
theorem hypersurface_section_of_closedPoint_degree_four
    {k : Type u} [Field k] [CharZero k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 4) :
    ∃ q : Spec (.of k) ⟶ hypersurface p hp, q ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  apply hypersurface_section_of_effective_degree_four p hp (Finsupp.single x 1)
  simpa [EffectiveZeroCycle.degree] using hx

/-- A finite closed subscheme of rank four on an actual projective cubic
surface in characteristic zero gives a rational point. Nonreduced subschemes
are included, since their local lengths contribute to the fundamental cycle. -/
theorem hypersurface_section_of_finite_closed_subscheme_rank_four
    {k : Type u} [Field k] [CharZero k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : finiteSchemeRank (i ≫ hypersurfaceToBase p hp) = 4) :
    ∃ q : Spec (.of k) ⟶ hypersurface p hp, q ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_of_finite_closed_subscheme i
    (hypersurfaceToBase p hp)
  exact hypersurface_section_of_effective_degree_four p hp z (hz.trans hi)

end HomogeneousProjective
end AllCharacteristics
