import PfaffianDescent.ActualPointLocalAdjunctionSectionEvaluation

/-! SOURCE ONLY, UNVERIFIED. Naturality of the genuine local point class
for arbitrary actual module maps, with no comparison certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.isDefEq.respectTransparency false

lemma actualPointLocalSectionClass_naturality
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) {M N : X.Modules} (a : M ⟶ N)
    (U : X.Opens) (hU : q ⁻¹ᵁ U = ⊤) (z : M.val.obj (op U)) :
    (moduleSpecΓFunctor (R := .of L)).map ((Scheme.Modules.pullback q).map a)
      (actualPointLocalSectionClass q M U hU z) =
    actualPointLocalSectionClass q N U hU (a.val.app (op U) z) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction q
  have ha : adj.homEquiv M ((Scheme.Modules.pullback q).obj N)
      ((Scheme.Modules.pullback q).map a) = a ≫ adj.unit.app N := by
    rw [Adjunction.homEquiv_unit]
    exact (adj.unit.naturality a).symm
  rw [actualPointLocalAdjunctionSectionEvaluation, ha]
  rfl

end PfaffianDescent
