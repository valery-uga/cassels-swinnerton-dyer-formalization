import PfaffianDescent.SchemeModuleFixedFrameGlobalSectionReconstruction
import PfaffianDescent.SchemeClosedPointNeighborhoodCover

/-! The SAME original global field image from actual closed-point stalks.
Actual closed-point representatives cover by compactness, so they give
actual preimages at ALL points; genuine existing gluing reconstructs.
No cohomology or closed-point-only image certificate is assumed.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [CompactSpace X]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- On the SAME compact integral scheme, the ORIGINAL global field-image
condition is detected at EVERY actual closed point. Actual local germ
representatives form a cover, then original germ laws produce all-stalk
membership and the genuine global reconstruction theorem applies. -/
theorem schemeModuleTopSectionsToFunctionFieldLinearMap_mem_range_iff_closedPointStalkRange
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M)
    (C : X.Opens) (hgC : genericPoint X ∈ C)
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (f : X.functionField) :
    letI : Nonempty C := ⟨⟨genericPoint X, hgC⟩⟩
    f ∈ Set.range (schemeModuleTopSectionsToFunctionFieldLinearMap pi M C hgC e) ↔
      ∀ P : closedPoints X,
        letI := schemeModuleStalkModule M P.1
        f ∈ Set.range (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C e P.1) := by
  classical
  letI : Nonempty C := ⟨⟨genericPoint X, hgC⟩⟩
  constructor
  · intro h P
    exact (schemeModuleTopSectionsToFunctionFieldLinearMap_mem_range_iff_stalkRange
      pi M hM C hgC e f).mp h P.1
  · intro h
    have hlocal : ∀ P : closedPoints X,
        ∃ (U : X.Opens) (hPU : P.1 ∈ U) (s : M.val.obj (op U)),
          letI : Nonempty U := ⟨⟨P.1, hPU⟩⟩
          (schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C e U s : X.functionField) = f := by
      intro P
      letI := schemeModuleStalkModule M P.1
      obtain ⟨a, ha⟩ := h P
      obtain ⟨U, hPU, s, rfl⟩ := M.presheaf.exists_germ_eq a
      refine ⟨U, hPU, s, ?_⟩
      letI : Nonempty U := ⟨⟨P.1, hPU⟩⟩
      exact (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi M C e P.1 U hPU s).symm.trans ha
    choose U hU s hs using hlocal
    have hcover : (⊤ : X.Opens) ≤ ⨆ P, U P := schemeClosedPointNeighborhoods_cover_top X U hU
    apply (schemeModuleTopSectionsToFunctionFieldLinearMap_mem_range_iff_stalkRange
      pi M hM C hgC e f).mpr
    intro x
    letI := schemeModuleStalkModule M x
    obtain ⟨P, hxUP⟩ := (Opens.mem_iSup).mp (hcover (show x ∈ (⊤ : X.Opens) from trivial))
    letI : Nonempty (U P) := ⟨⟨P.1, hU P⟩⟩
    exact ⟨M.presheaf.germ (U P) x hxUP (s P),
      (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi M C e x (U P) hxUP (s P)).trans (hs P)⟩

end PfaffianDescent
