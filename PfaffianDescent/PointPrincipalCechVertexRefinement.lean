import PfaffianDescent.PointPrincipalCechAssembly
import PfaffianDescent.SectionRepresenterCechVertexRefinement

/-! # The principal-cover comparison refines the original point vertex map -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace PfaffianDescent.PointAdaptedAffineCover
universe u

set_option backward.isDefEq.respectTransparency false in
/-- The principal degree-zero map is exactly the refinement of the original
point-adapted degree-zero map. -/
theorem principalOnC₀_refinement
    {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    (hq : X.presheaf.germ U x hx q ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hf : X.presheaf.germ U x hx f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    (principalToAdaptedChain U hU x hx q f hq hf).f 0 ≫ onC₀ U x =
      principalOnC₀ U x q f := by
  let σ := principalToAdaptedIndex U hU x hx q f hq hf
  let j : ∀ i, principalOpens U x q f i ⟶ opens U x (σ i) :=
    fun i => homOfLE (le_of_eq (principalToAdaptedIndex_opens U hU x hx q f hq hf i).symm)
  change (sectionRepresenterCechRefinement X.ringCatSheaf (opens U x)
      (principalOpens U x q f) σ j).f 0 ≫
      sectionRepresenterCechVertexMap X.ringCatSheaf (opens U x)
        (sectionRepresenter X.ringCatSheaf U) (vertexMap U x) =
    sectionRepresenterCechVertexMap X.ringCatSheaf (principalOpens U x q f)
      (sectionRepresenter X.ringCatSheaf U) (principalVertexMap U x q f)
  rw [sectionRepresenterCechVertexMap_refinement]
  congr 1
  funext i
  cases i with
  | inl k =>
    fin_cases k
    · change ((sectionRepresenterFunctor X.ringCatSheaf).map (j (Sum.inl 0)) :
        sectionRepresenter X.ringCatSheaf (X.basicOpen q) ⟶
          sectionRepresenter X.ringCatSheaf (X.basicOpen q)) ≫
        (0 : sectionRepresenter X.ringCatSheaf (X.basicOpen q) ⟶
          sectionRepresenter X.ringCatSheaf U) = 0
      simp only [comp_zero]
    · change ((sectionRepresenterFunctor X.ringCatSheaf).map (j (Sum.inl 1)) :
        sectionRepresenter X.ringCatSheaf (X.basicOpen f) ⟶
          sectionRepresenter X.ringCatSheaf (X.basicOpen f)) ≫
        (0 : sectionRepresenter X.ringCatSheaf (X.basicOpen f) ⟶
          sectionRepresenter X.ringCatSheaf U) = 0
      simp only [comp_zero]
  | inr i =>
    have hj : j (Sum.inr i) = 𝟙 (opens U x i) := Subsingleton.elim _ _
    change (sectionRepresenterFunctor X.ringCatSheaf).map (j (Sum.inr i)) ≫
      vertexMap U x i = vertexMap U x i
    rw [hj]
    have hid : ((sectionRepresenterFunctor X.ringCatSheaf).map (𝟙 (opens U x i)) :
        sectionRepresenter X.ringCatSheaf (opens U x i) ⟶
          sectionRepresenter X.ringCatSheaf (opens U x i)) = 𝟙 _ :=
      CategoryTheory.Functor.map_id _ _
    exact (congrArg (fun k : sectionRepresenter X.ringCatSheaf (opens U x i) ⟶
      sectionRepresenter X.ringCatSheaf (opens U x i) => k ≫ vertexMap U x i) hid).trans
        (Category.id_comp _)

end PfaffianDescent.PointAdaptedAffineCover
