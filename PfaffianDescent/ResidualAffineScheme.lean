import PfaffianDescent.ResidualAlgebraLength
import PfaffianDescent.ResidualCycles
import AllCharacteristics.FiniteFlatCycle

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
universe u
section
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]

/-- The actual closed residual subscheme cut out by the annihilator ideal. -/
noncomputable def residualAffineι (P : Ideal A) :
    Spec (.of (A ⧸ residualAlgebraIdeal P)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (residualAlgebraIdeal P)))

instance residualAffineι_isClosedImmersion (P : Ideal A) : IsClosedImmersion (residualAffineι P) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

lemma residualAffineι_toBase (P : Ideal A) :
    residualAffineι P ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (A ⧸ residualAlgebraIdeal P))) := by
  rw [residualAffineι, ← Spec.map_comp]
  rfl

instance residualAffine_toBase_isFinite (P : Ideal A) :
    IsFinite (residualAffineι P ≫ Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
  rw [residualAffineι_toBase]
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The residual subscheme of a length-five quotient in a length-six finite
algebra has actual scheme rank one. -/
theorem residual_affine_scheme_length_one (P : Ideal A)
    (hA : finrank K A = 6) (hP : finrank K (A ⧸ P) = 5) :
    AllCharacteristics.finiteSchemeRank
      (residualAffineι P ≫ Spec.map (CommRingCat.ofHom (algebraMap K A))) = 1 := by
  rw [AllCharacteristics.finiteSchemeRank_eq_finrank, residualAffineι_toBase,
    Scheme.Hom.finrank_SpecMap_algebraMap]
  exact (congrFun (Module.rankAtStalk_eq_finrank_of_free
    (R := K) (M := A ⧸ residualAlgebraIdeal P)) _).trans
      (residual_algebra_six_minus_five P hA hP)

/-- The residual degree-one subscheme supplies a rational point of the
ambient finite scheme, with its factorization through the residual inclusion. -/
theorem residual_affine_scheme_section (P : Ideal A)
    (hA : finrank K A = 6) (hP : finrank K (A ⧸ P) = 5) :
    ∃ s : Spec (.of K) ⟶ Spec (.of (A ⧸ residualAlgebraIdeal P)),
      s ≫ residualAffineι P ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) = 𝟙 _ := by
  obtain ⟨z, hz⟩ := AllCharacteristics.exists_effectiveZeroCycle_degree_finiteSchemeRank
    (residualAffineι P ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)))
  apply section_of_effective_cycle_degree_one _ z
  exact hz.trans (residual_affine_scheme_length_one P hA hP)

end
end PfaffianDescent
