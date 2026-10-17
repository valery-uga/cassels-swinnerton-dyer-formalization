import PfaffianDescent.VoisinCartierInverseTwist
import PfaffianDescent.ClosedImmersionIdealModuleLocallyFree

/-!
# Twisting a Serre extension by an actual Cartier ideal

The regular-principal charts themselves give the local unit trivializations
required for exactness after tensoring. Thus vanishing of global sections
of the inverse Cartier twist supplies the section injection in the twisted
Serre sequence without an additional abstract cover hypothesis.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

theorem SerreExtensionSequenceData.twistedProjection_sections_injective_of_cartier
    {X Z : Scheme.{u}} {M : SheafOfModules.{u} X.ringCatSheaf}
    {i : Z ⟶ X} [IsClosedImmersion i]
    (e : SerreExtensionSequenceData X M)
    (H : RegularPrincipalImmersion i)
    [Subsingleton H.inverseCartierTwist.sections] :
    Function.Injective (SheafOfModules.sectionsMap
      (e.twistedComplex H.inverseCartierTwist).g) := by
  let C : ULift.{u} H.Index → X.affineOpens := fun j => by
    letI : IsOpenImmersion (H.target j.down) := H.targetOpen j.down
    let W : (Spec (H.A j.down)).affineOpens :=
      ⟨⊤, isAffineOpen_top (Spec (H.A j.down))⟩
    exact ⟨H.target j.down ''ᵁ W, W.2.image_of_isOpenImmersion _⟩
  have hcover : (Opens.grothendieckTopology X).CoversTop
      (fun j : ULift.{u} H.Index => (C j).1) := by
    apply (Opens.coversTop_iff _ _).mpr
    apply TopologicalSpace.IsOpenCover.mk
    apply le_antisymm le_top
    intro x _
    obtain ⟨j, y, hy⟩ := H.cover x
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨ULift.up j, ?_⟩
    letI : IsOpenImmersion (H.target j) := H.targetOpen j
    change x ∈ H.target j ''ᵁ ⊤
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact Scheme.Hom.mem_opensRange.mpr ⟨y, hy⟩
  apply e.twistedProjection_sections_injective_of_subsingleton_twist
    (fun j : ULift.{u} H.Index => (C j).1) hcover
  intro j
  letI : IsOpenImmersion (H.target j.down) := H.targetOpen j.down
  let f := H.chartIdealModuleHom j.down
  let U : X.Opens := (C j).1
  let e₀ : SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf ≅
      H.inverseCartierTwist.restrict U.ι :=
    @asIso _ _ _ _ f (H.chartIdealModuleHom_isIso j.down)
  exact ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit U e₀.symm

end PfaffianDescent
