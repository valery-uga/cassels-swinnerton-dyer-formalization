import PfaffianDescent.VoisinDegreeElevenSerreIncidencePulledFreeOver
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeMatrix

/-! # Actual pullback retains the displayed local rank-two presentation -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidencePulled_locallyFree
    {X Y : Scheme.{u}} (f : Y ⟶ X) {N : X.Modules}
    (e : SerreExtensionData X N) (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e) :
    ((Scheme.Modules.pullback f).obj (show X.Modules from e.E)).IsLocallyFree := by
  apply sheaf_isLocallyFree_of_coverIso _ _ (fun i => f ⁻¹ᵁ C.U i) ?_
    (fun _ => ULift.{u} (Fin 2))
    (fun i => serreIncidencePulledFreeOverIso f
      (show X.Modules from e.E) (C.U i) _ (C.trivialization i))
  exact (Opens.coversTop_iff _ _).mpr (by
    apply TopologicalSpace.IsOpenCover.mk
    rw [← Scheme.Hom.preimage_iSup, C.covers, Scheme.Hom.preimage_top])

end PfaffianDescent
