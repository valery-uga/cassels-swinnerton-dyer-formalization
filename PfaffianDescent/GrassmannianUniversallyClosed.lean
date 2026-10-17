import PfaffianDescent.GrassmannianValuationExtension
import PfaffianDescent.GrassmannianFiniteType
import Mathlib.AlgebraicGeometry.ValuativeCriterion

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K]

/-- The Grassmannian structure morphism satisfies the existence part of the valuative criterion. -/
theorem grassmannianToBase_valuativeExistence (m n : ℕ) :
    ValuativeCriterion.Existence (grassmannianToBase K m n) := by
  intro S
  let ψ := Spec.preimage S.i₂
  letI : Algebra K S.R := ψ.hom.toAlgebra
  letI : Algebra K S.K := ((algebraMap S.R S.K).comp ψ.hom).toAlgebra
  letI : IsScalarTower K S.R S.K := IsScalarTower.of_algebraMap_eq' rfl
  have hb : Spec.map (CommRingCat.ofHom (algebraMap K S.R)) = S.i₂ := Spec.map_preimage S.i₂
  have hf : S.i₁ ≫ grassmannianToBase K m n = Spec.map (CommRingCat.ofHom (algebraMap K S.K)) := by
    calc
      S.i₁ ≫ grassmannianToBase K m n = Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ S.i₂ := S.commSq.w
      _ = Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap K S.R)) :=
        congrArg (fun g => Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ g) hb.symm
      _ = _ := by rw [← Spec.map_comp]; rfl
  obtain ⟨g, hg, hgb⟩ := grassmannian_valuation_extension K (R := S.R) S.i₁ hf
  exact ⟨⟨{ l := g, fac_left := hg, fac_right := hgb.trans hb }⟩⟩

/-- The global Grassmannian is universally closed over every coefficient ring. -/
instance grassmannianToBase_universallyClosed (m n : ℕ) : UniversallyClosed (grassmannianToBase K m n) :=
  UniversallyClosed.of_valuativeCriterion _ (grassmannianToBase_valuativeExistence K m n)

end
end PfaffianDescent
