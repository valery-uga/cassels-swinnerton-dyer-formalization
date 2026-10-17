import PfaffianDescent.VoisinDegreeElevenSerreIncidenceFlatPulledSequence
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceFieldPulledLocallyFree

/-! # The actual Serre extension over the field-extended surface -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def serreIncidenceFieldPulledSerre
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of K)) (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e) :
    SerreExtensionData (schemeFieldBaseChange (L := L) base)
      ((Scheme.Modules.pullback (schemeFieldBaseChangeToOriginal (L := L) base)).obj N) := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  letI : Flat g := inferInstanceAs (Flat (CategoryTheory.Limits.pullback.fst base
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))))
  exact SerreExtensionData.ofSequence (serreIncidenceFlatPulledSequence g e)
    (serreIncidenceFieldPulled_locallyFree base e C)

@[simp]
theorem serreIncidenceFieldPulledSerre_middle
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of K)) (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e) :
    (serreIncidenceFieldPulledSerre (L := L) base e C).E =
      (Scheme.Modules.pullback (schemeFieldBaseChangeToOriginal (L := L) base)).obj
        (show X.Modules from e.E) := rfl

end PfaffianDescent
