import PfaffianDescent.GoodFiberAlgebraEquiv
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

section
variable (K : Type u) [Field K] [NeZero (2 : K)]

/-- The scheme defined by the three displayed affine incidence equations. -/
noncomputable def goodFiberScheme : Scheme.{u} := Spec (.of (GoodFiberAlgebra K))

noncomputable def goodFiberToBase : goodFiberScheme K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (GoodFiberAlgebra K)))

instance : IsFinite (goodFiberToBase K) := by
  apply (IsFinite.SpecMap_iff _).mpr
  change (algebraMap K (GoodFiberAlgebra K)).Finite
  exact RingHom.finite_algebraMap.mpr inferInstance

instance : Etale (goodFiberToBase K) := by
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
  exact (RingHom.etale_algebraMap).mpr inferInstance

lemma goodFiberToBase_finrank (x : Spec (.of K)) : (goodFiberToBase K).finrank x = 2 := by
  change (Spec.map (CommRingCat.ofHom (algebraMap K (GoodFiberAlgebra K)))).finrank x = 2
  have hr := Scheme.Hom.finrank_SpecMap_algebraMap K (GoodFiberAlgebra K) x
  have hd := congrFun (Module.rankAtStalk_eq_finrank_of_free
    (R := K) (M := GoodFiberAlgebra K)) x
  exact hr.trans (hd.trans GoodFiberAlgebra.finrank_eq_two)

/-- The displayed affine incidence fiber is a finite étale scheme of degree two.
This retains the full quotient scheme structure, not just its field-valued points. -/
theorem goodFiber_finite_etale_degree_two :
    IsFinite (goodFiberToBase K) ∧ Etale (goodFiberToBase K) ∧
      ∀ x : Spec (.of K), (goodFiberToBase K).finrank x = 2 :=
  ⟨inferInstance, inferInstance, goodFiberToBase_finrank K⟩

end
end PfaffianDescent
