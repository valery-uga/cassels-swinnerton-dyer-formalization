import PfaffianDescent.IncidenceGraphChart
import PfaffianDescent.IncidenceGraphFormula
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Types.Basic

namespace PfaffianDescent
open Module CategoryTheory Opposite
section
variable {R S : Type*} [CommRing R] [CommRing S]

lemma incidenceGraphPointCoordinates_symm_graph (c : IncidenceGraphIndex → R)
    (x : Fin 3 → R) (i : Fin 3) :
    ((incidenceGraphPointCoordinates R).symm c).1 x i =
      ∑ j, c (Sum.inl (i, j)) * x j := rfl

lemma incidenceGraphPointCoordinates_symm_form (c : IncidenceGraphIndex → R)
    (i : Fin 3) :
    (((incidenceGraphPointCoordinates R).symm c).2 i).1 =
      ((incidenceGraphKernelCoordinates ((incidenceGraphPointCoordinates R).symm c).1).symm
        (fun j => c (Sum.inr (i, j)))).1 := rfl

lemma incidenceGraphPointCoordinates_graph_map (φ : R →+* S) (c : IncidenceGraphIndex → R)
    (x : Fin 3 → R) :
    ((incidenceGraphPointCoordinates S).symm (φ ∘ c)).1 (φ ∘ x) =
      φ ∘ ((incidenceGraphPointCoordinates R).symm c).1 x := by
  funext i
  simp [incidenceGraphPointCoordinates_symm_graph, map_sum, map_mul]

/-- Every reconstructed form is compatible with extension of coefficient rings. -/
lemma incidenceGraphPointCoordinates_form_map (φ : R →+* S) (c : IncidenceGraphIndex → R)
    (i : Fin 3) (x y : (Fin 3 → R) × (Fin 3 → R)) :
    (((incidenceGraphPointCoordinates S).symm (φ ∘ c)).2 i).1
      ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] =
        φ ((((incidenceGraphPointCoordinates R).symm c).2 i).1 ![x, y]) := by
  rw [incidenceGraphPointCoordinates_symm_form, incidenceGraphPointCoordinates_symm_form]
  exact incidenceGraphKernelCoordinates_symm_map φ _ _
    (incidenceGraphPointCoordinates_graph_map φ c) (fun j => c (Sum.inr (i, j))) x y

/-- Extension of coefficients for the graph and its common-isotropic triple. -/
noncomputable def incidenceGraphPointMap (φ : R →+* S) (p : IncidenceGraphPoints R) :
    IncidenceGraphPoints S :=
  (incidenceGraphPointCoordinates S).symm (φ ∘ incidenceGraphPointCoordinates R p)

@[simp] lemma incidenceGraphPointMap_coordinates (φ : R →+* S) (p : IncidenceGraphPoints R) :
    incidenceGraphPointCoordinates S (incidenceGraphPointMap φ p) =
      φ ∘ incidenceGraphPointCoordinates R p :=
  (incidenceGraphPointCoordinates S).apply_symm_apply _

lemma incidenceGraphPointMap_graph (φ : R →+* S) (p : IncidenceGraphPoints R)
    (x : Fin 3 → R) :
    (incidenceGraphPointMap φ p).1 (φ ∘ x) = φ ∘ p.1 x := by
  have h := incidenceGraphPointCoordinates_graph_map φ (incidenceGraphPointCoordinates R p) x
  simpa only [incidenceGraphPointMap, Equiv.symm_apply_apply] using h

lemma incidenceGraphPointMap_form (φ : R →+* S) (p : IncidenceGraphPoints R)
    (i : Fin 3) (x y : (Fin 3 → R) × (Fin 3 → R)) :
    ((incidenceGraphPointMap φ p).2 i).1
      ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] = φ ((p.2 i).1 ![x, y]) := by
  have h := incidenceGraphPointCoordinates_form_map φ (incidenceGraphPointCoordinates R p) i x y
  have he := congrArg (fun q : IncidenceGraphPoints R => (q.2 i).1 ![x, y])
    ((incidenceGraphPointCoordinates R).symm_apply_apply p)
  exact h.trans (congrArg φ he)

@[simp] lemma incidenceGraphPointMap_id (p : IncidenceGraphPoints R) :
    incidenceGraphPointMap (RingHom.id R) p = p := by
  apply (incidenceGraphPointCoordinates R).injective
  simp

lemma incidenceGraphPointMap_comp {T : Type*} [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (p : IncidenceGraphPoints R) :
    incidenceGraphPointMap ψ (incidenceGraphPointMap φ p) =
      incidenceGraphPointMap (ψ.comp φ) p := by
  apply (incidenceGraphPointCoordinates T).injective
  simp only [incidenceGraphPointMap_coordinates]
  rfl

end

universe u
section
variable (K : Type u) [CommRing K]

/-- The common-isotropic graph-chart functor, with coefficient maps verified
on the graph and on all values of the alternating forms. -/
noncomputable def incidenceGraphFunctor : CommAlgCat.{u} K ⥤ Type u where
  obj A := IncidenceGraphPoints A
  map f := TypeCat.ofHom (incidenceGraphPointMap f.hom.toRingHom)
  map_id A := by
    apply ConcreteCategory.hom_ext
    intro p
    exact incidenceGraphPointMap_id p
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    exact (incidenceGraphPointMap_comp f.hom.toRingHom g.hom.toRingHom p).symm

/-- The coordinate ring has precisely the algebra-valued common-isotropic graph points. -/
noncomputable def incidenceGraphAlgHomEquiv (A : Type u) [CommRing A] [Algebra K A] :
    (IncidenceGraphRing K →ₐ[K] A) ≃ IncidenceGraphPoints A :=
  ({ toFun := fun h j => h (MvPolynomial.X j)
     invFun := MvPolynomial.aeval
     left_inv := fun h => MvPolynomial.algHom_ext
       (fun j => MvPolynomial.aeval_X (fun k => h (MvPolynomial.X k)) j)
     right_inv := fun c => funext (fun j => MvPolynomial.aeval_X c j) } :
      (IncidenceGraphRing K →ₐ[K] A) ≃ (IncidenceGraphIndex → A)).trans
    (incidenceGraphPointCoordinates A).symm

lemma incidenceGraphAlgHomEquiv_coordinates (A : Type u) [CommRing A] [Algebra K A]
    (h : IncidenceGraphRing K →ₐ[K] A) :
    incidenceGraphPointCoordinates A (incidenceGraphAlgHomEquiv K A h) =
      fun j => h (MvPolynomial.X j) :=
  (incidenceGraphPointCoordinates A).apply_symm_apply _

/-- The graph incidence functor is represented by the affine forty-five-parameter algebra.
Naturality uses coefficient extension verified on the actual graph and forms above. -/
noncomputable def incidenceGraphCorepresentable :
    (incidenceGraphFunctor K).CorepresentableBy (CommAlgCat.of K (IncidenceGraphRing K)) where
  homEquiv {A} := ConcreteCategory.homEquiv.trans (incidenceGraphAlgHomEquiv K A)
  homEquiv_comp {A B} g f := by
    apply (incidenceGraphPointCoordinates B).injective
    change incidenceGraphPointCoordinates B (incidenceGraphAlgHomEquiv K B (g.hom.comp f.hom)) =
      incidenceGraphPointCoordinates B
        (incidenceGraphPointMap g.hom.toRingHom (incidenceGraphAlgHomEquiv K A f.hom))
    rw [incidenceGraphPointMap_coordinates, incidenceGraphAlgHomEquiv_coordinates,
      incidenceGraphAlgHomEquiv_coordinates]
    rfl

end
end PfaffianDescent
