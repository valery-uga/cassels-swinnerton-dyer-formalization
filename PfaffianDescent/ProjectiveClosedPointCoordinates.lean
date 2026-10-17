import PfaffianDescent.NormalizedProjectiveClosedPoint

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K L : Type u} [Field K] [Field L] [Algebra K L] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A closed field-valued projective point factors through a coordinate chart
by a surjective coordinate-ring homomorphism. -/
theorem closed_projective_point_chart
    (I : HomogeneousIdeal (homogeneousSubmodule σ K))
    (q : Spec (.of L) ⟶ scheme I) [IsClosedImmersion q]
    (hq : q ≫ toBase I = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    ∃ j : σ, ∃ g : ChartRing I j →+* L, Function.Surjective g ∧
      g.comp (chartBaseMap I j) = algebraMap K L ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι I j = q := by
  obtain ⟨j, y, hy⟩ := exists_coordinate_chart I (q (IsLocalRing.closedPoint L))
  have hrange : Set.range q ⊆ Set.range (chartι I j) := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint L := Subsingleton.elim _ _
    exact ⟨y, hy.trans (congrArg q hp).symm⟩
  let qU := IsOpenImmersion.lift (chartι I j) q hrange
  have hU : qU ≫ chartι I j = q := IsOpenImmersion.lift_fac _ _ _
  have : IsClosedImmersion (qU ≫ chartι I j) := hU.symm ▸ inferInstance
  have : IsClosedImmersion qU := IsClosedImmersion.of_comp qU (chartι I j)
  let g := Spec.preimage qU
  have hg : Spec.map g = qU := Spec.map_preimage qU
  refine ⟨j, g.hom, AllCharacteristics.spec_preimage_surjective_of_closedImmersion qU, ?_, ?_⟩
  · have he : CommRingCat.ofHom (chartBaseMap I j) ≫ g =
        CommRingCat.ofHom (algebraMap K L) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hg, ← chartι_toBase, ← Category.assoc, hU, hq]
    exact congrArg CommRingCat.Hom.hom he
  · exact (congrArg (· ≫ chartι I j) hg).trans hU

/-- Normalized coordinates of an actual closed projective point generate its
whole residue field as an algebra; this loses no field-of-definition data. -/
theorem closed_projective_point_generating_coordinates
    (I : HomogeneousIdeal (homogeneousSubmodule σ K))
    (q : Spec (.of L) ⟶ scheme I) [IsClosedImmersion q]
    (hq : q ≫ toBase I = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    ∃ j : σ, ∃ x : σ → L, x j = 1 ∧ Function.Surjective (eval₂Hom (algebraMap K L) x) ∧
      ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K L) x = 0 := by
  obtain ⟨j, g, hgs, hg, _⟩ := closed_projective_point_chart I q hq
  let x : σ → L := fun k => g (chartCoordinate I j k)
  have he : eval₂Hom (algebraMap K L) x =
      g.comp (eval₂Hom (chartBaseMap I j) (chartCoordinate I j)) := by
    apply RingHom.ext
    intro p
    change p.eval₂ (algebraMap K L) x = g (p.eval₂ (chartBaseMap I j) (chartCoordinate I j))
    rw [hom_eval₂, hg]
  refine ⟨j, x, ?_, ?_, ?_⟩
  · change g (chartCoordinate I j j) = 1
    rw [chartCoordinate_self, map_one]
  · rw [he]
    exact hgs.comp (eval₂_chartCoordinate_surjective I j)
  · intro p hp
    change eval₂Hom (algebraMap K L) x p = 0
    rw [he, RingHom.comp_apply]
    rw [show eval₂Hom (chartBaseMap I j) (chartCoordinate I j) p = 0 from
      eval₂_chartCoordinate_eq_zero_of_mem I j p hp, map_zero]

end
end PfaffianDescent
