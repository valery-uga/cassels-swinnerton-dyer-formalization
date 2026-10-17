import PfaffianDescent.IncidenceGraphCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

namespace PfaffianDescent
open Module AlgebraicGeometry CategoryTheory

/-- The forty-five free parameters: nine graph entries and thirty-six fiber entries. -/
abbrev IncidenceGraphIndex := (Fin 3 × Fin 3) ⊕ (Fin 3 × IncidenceKernelIndex)

noncomputable instance : Fintype IncidenceGraphIndex := Fintype.ofFinite _

lemma incidenceGraphIndex_card : Fintype.card IncidenceGraphIndex = 45 := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card ((Fin 3 × Fin 3) ⊕ (Fin 3 × IncidenceKernelIndex)) = 45
  rw [Nat.card_sum, Nat.card_prod, Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, incidenceKernelIndex_card]

section
variable (R : Type*) [CommRing R]

/-- Actual common-isotropic triples over an arbitrary ring in one Grassmannian chart. -/
def GrassmannianGraphIncidence :=
  Σ W : GrassmannianGraphChart R 3 3,
    Fin 3 → LinearMap.ker
      (alternatingRestriction R ((Fin 3 → R) × (Fin 3 → R)) W.1.toSubmodule)

/-- Graphs and their isotropic triples before replacing graphs by Grassmannian points. -/
abbrev IncidenceGraphPoints := Σ f : (Fin 3 → R) →ₗ[R] (Fin 3 → R), IncidenceGraphFiber f

noncomputable def incidenceGraphPointsEquiv :
    IncidenceGraphPoints R ≃ GrassmannianGraphIncidence R :=
  Equiv.sigmaCongrLeft
    (β := fun W : GrassmannianGraphChart R 3 3 => Fin 3 → LinearMap.ker
      (alternatingRestriction R ((Fin 3 → R) × (Fin 3 → R)) W.1.toSubmodule))
    (grassmannianGraphChartEquiv (R := R) (m := 3) (n := 3))

/-- All ring-valued points of the chart have forty-five unrestricted coordinates. -/
noncomputable def incidenceGraphPointCoordinates :
    IncidenceGraphPoints R ≃ (IncidenceGraphIndex → R) :=
  (Equiv.sigmaEquivProdOfEquiv (fun f => (incidenceGraphFiberCoordinates f).toEquiv)).trans
    ((Equiv.prodCongr
      (Matrix.toLin'.symm.toEquiv.trans
        { toFun := fun t ij => t ij.1 ij.2
          invFun := fun t i j => t (i, j)
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl })
      { toFun := fun t ij => t ij.1 ij.2
        invFun := fun t i j => t (i, j)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }).trans
          (Equiv.sumArrowEquivProdArrow _ _ R).symm)

/-- The same parameterization, stated for actual quotient-Grassmannian objects. -/
noncomputable def grassmannianGraphIncidenceCoordinates :
    GrassmannianGraphIncidence R ≃ (IncidenceGraphIndex → R) :=
  (incidenceGraphPointsEquiv R).symm.trans (incidenceGraphPointCoordinates R)

end

universe u
section
variable (K : Type u) [CommRing K]

/-- The polynomial ring of the standard incidence chart. -/
abbrev IncidenceGraphRing := MvPolynomial IncidenceGraphIndex K

/-- Universal graph and universal isotropic forms over the chart coordinate ring. -/
noncomputable def incidenceGraphUniversal : IncidenceGraphPoints (IncidenceGraphRing K) :=
  (incidenceGraphPointCoordinates (IncidenceGraphRing K)).symm MvPolynomial.X

lemma incidenceGraphUniversal_coordinates :
    incidenceGraphPointCoordinates (IncidenceGraphRing K) (incidenceGraphUniversal K) =
      MvPolynomial.X :=
  (incidenceGraphPointCoordinates (IncidenceGraphRing K)).apply_symm_apply _

/-- The universal triple vanishes on its actual graph submodule. -/
lemma incidenceGraphUniversal_isotropic (i : Fin 3) :
    alternatingRestriction (IncidenceGraphRing K)
      ((Fin 3 → IncidenceGraphRing K) × (Fin 3 → IncidenceGraphRing K))
      (incidenceGraphUniversal K).1.graph ((incidenceGraphUniversal K).2 i).1 = 0 :=
  ((incidenceGraphUniversal K).2 i).2

/-- The affine parameter scheme for the standard incidence chart. -/
noncomputable def incidenceGraphScheme : Scheme.{u} := Spec (.of (IncidenceGraphRing K))

noncomputable def incidenceGraphToBase : incidenceGraphScheme K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (IncidenceGraphRing K)))

instance incidenceGraphToBase_smooth : Smooth (incidenceGraphToBase K) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  apply RingHom.smooth_algebraMap.mpr
  change Algebra.Smooth K (MvPolynomial IncidenceGraphIndex K)
  exact ⟨inferInstance, inferInstance⟩

end
end PfaffianDescent
