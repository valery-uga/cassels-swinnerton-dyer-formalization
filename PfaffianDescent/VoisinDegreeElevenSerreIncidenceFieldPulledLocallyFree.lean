import PfaffianDescent.VoisinDegreeElevenSerreIncidenceFieldPulledFreeOver
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeMatrix

/-! # The actual field-pulled Serre bundle is locally free -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceFieldPulled_locallyFree
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of K)) (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e) :
    ((Scheme.Modules.pullback (schemeFieldBaseChangeToOriginal (L := L) base)).obj
      (show X.Modules from e.E)).IsLocallyFree := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  apply sheaf_isLocallyFree_of_coverIso _ _ (fun i => g ⁻¹ᵁ C.U i) ?_
    (fun _ => ULift.{u} (Fin 2))
    (fun i => serreIncidenceFieldPulledFreeOverIso (L := L) base
      (show X.Modules from e.E) (C.U i) _ (C.trivialization i))
  exact (Opens.coversTop_iff _ _).mpr (by
    apply TopologicalSpace.IsOpenCover.mk
    rw [← Scheme.Hom.preimage_iSup, C.covers, Scheme.Hom.preimage_top])

end PfaffianDescent
