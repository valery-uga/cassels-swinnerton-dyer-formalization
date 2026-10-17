import PfaffianDescent.SerreActualChosenMarkedResidualGeometry
import PfaffianDescent.SerreActualChosenMarkedParameterAssociationPointSurface

/-! Assemble chosen marked geometry after the actual field and support point
have been derived. The parameter association is handled once here. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

def serreActualChosenMarkedResidualGeometry_of_section
    {F E L : Type u} [Field F] [Field E] [Field L] [Algebra F E]
    {X P Q Z I : Scheme.{u}}
    (x : X ⟶ Spec (.of F)) (pp : P ⟶ Spec (.of F))
    (qp : Q ⟶ Spec (.of F)) (zero : Z ⟶ pullback x pp)
    (i : I ⟶ X) (j : Spec (.of L) ⟶ X)
    (q : Spec (.of F) ⟶ Q) (hq : q ≫ qp = 𝟙 _)
    (v : Q ⟶ P) (hv : v ≫ pp = qp)
    (δ : Fin 3 → (Spec (.of E) ⟶ pullback (zero ≫ pullback.snd x pp)
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v)))
    (hδ : ∀ n, δ n ≫ pullback.snd (zero ≫ pullback.snd x pp)
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v) = 𝟙 _)
    (n : Fin 3)
    (hf : IsField ((pullback (zero ≫ pullback.snd x pp)
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v)).presheaf.stalk
        ((δ n) (IsLocalRing.closedPoint E))))
    (hout : (serreActualChosenFibre_marked x pp zero
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v) δ n)
        (IsLocalRing.closedPoint E) ∉ Set.range i)
    (hpoint : (serreActualChosenFibre_marked x pp zero
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v) δ n)
        (IsLocalRing.closedPoint E) = j (IsLocalRing.closedPoint L)) :
    SerreActualChosenMarkedResidualGeometry x pp zero i j
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v) := by
  let r := Spec.map (CommRingCat.ofHom (algebraMap F E))
  let assocIso := serreActualChosenMarkedParameterAssociation
    (zero ≫ pullback.snd x pp) r q v
  let y := assocIso.hom ((δ n) (IsLocalRing.closedPoint E))
  have hy := serreActualChosenMarkedParameterAssociation_stalk_isField
    (zero ≫ pullback.snd x pp) r q v ((δ n) (IsLocalRing.closedPoint E)) hf
  have hySurface := serreActualChosenMarkedParameterAssociation_point_surface
    (zero ≫ pullback.snd x pp) r q v (zero ≫ pullback.fst x pp)
    ((δ n) (IsLocalRing.closedPoint E)) (j (IsLocalRing.closedPoint L)) hpoint
  have ht : (q ≫ v) ≫ pp = 𝟙 _ := by rw [Category.assoc, hv, hq]
  exact ⟨q ≫ v, ht, Category.assoc r q v, δ, hδ, n, hout, hpoint,
    y, hy, hySurface⟩

end PfaffianDescent
