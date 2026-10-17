import PfaffianDescent.PolynomialProjectiveMap
import PfaffianDescent.RectangularSubstitution

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K : Type u} [CommRing K] {m n d : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (M : Matrix (Fin m) (Fin n) K) (N : Matrix (Fin n) (Fin m) K) (hNM : N*M = 1)
    (f : MvPolynomial (Fin m) K) (hf : f.IsHomogeneous d)

lemma linearSection_ideal_le :
    (equationIdeal f hf).toIdeal ≤
      (equationIdeal (rectangularSubstitution M f)
        (rectangularSubstitution_homogeneous M hf)).toIdeal.comap
          (rectangularSubstitution M).toRingHom := by
  change Ideal.span {f} ≤ _
  apply Ideal.span_le.mpr
  intro p hp
  obtain rfl := Set.mem_singleton_iff.mp hp
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The actual hypersurface in the linear subspace: its equation is the
homogeneous restriction of the original equation. -/
noncomputable abbrev linearHypersurfaceSection :=
  hypersurface (rectangularSubstitution M f) (rectangularSubstitution_homogeneous M hf)

/-- The closed embedding of the hypersurface's linear section into the original
hypersurface, induced by the split linear inclusion. -/
noncomputable def linearHypersurfaceSectionι :
    linearHypersurfaceSection M f hf ⟶ hypersurface f hf :=
  polynomialProjectiveMap (equationIdeal f hf)
    (equationIdeal (rectangularSubstitution M f) (rectangularSubstitution_homogeneous M hf))
    (rectangularSubstitution M) (linearSection_ideal_le M f hf)
    (fun _ _ hp => rectangularSubstitution_homogeneous M hp)
    (rectangularSubstitution_surjective M N hNM)

instance linearHypersurfaceSectionι_isClosedImmersion :
    IsClosedImmersion (linearHypersurfaceSectionι M N hNM f hf) :=
  polynomialProjectiveMap_isClosedImmersion _ _ _ _ _ _

/-- The linear-section embedding preserves the ground-field structure. -/
theorem linearHypersurfaceSectionι_toBase :
    linearHypersurfaceSectionι M N hNM f hf ≫ hypersurfaceToBase f hf =
      hypersurfaceToBase (rectangularSubstitution M f) (rectangularSubstitution_homogeneous M hf) :=
  polynomialProjectiveMap_toBase _ _ _ _ _ _

end
end PfaffianDescent
