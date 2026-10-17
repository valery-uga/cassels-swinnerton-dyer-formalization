import PfaffianDescent.VoisinDegreeElevenSerreIncidenceFieldPulledSerre

/-! # The actual inverse-image affine cover of the field-pulled Serre extension -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def serreIncidenceFieldPulledCover
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of K)) (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e) :
    SerreExtensionData.SerreExtensionRankTwoAffineCover
      (serreIncidenceFieldPulledSerre (L := L) base e C) where
  ι := C.ι
  U := fun i => schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ C.U i
  covers := (schemeFieldBaseChangeToOriginal (L := L) base).iSup_preimage_eq_top C.covers
  affine i := by
    letI := C.affine i
    exact isAffine_schemeFieldBaseChangeOpen (L := L) base (C.U i)
  overlapAffine i j := by
    letI := C.overlapAffine i j
    change IsAffine (schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ
      (C.U i ⊓ C.U j) : Scheme.{u})
    exact isAffine_schemeFieldBaseChangeOpen (L := L) base (C.U i ⊓ C.U j)
  trivialization i := serreIncidenceFieldPulledFreeOverIso (L := L) base
    (show X.Modules from e.E) (C.U i) (ULift.{u} (Fin 2)) (C.trivialization i)

end PfaffianDescent
