import PfaffianDescent.PointPrincipalCechVertexRefinement

/-! # The actual point augmentation on the principal cover -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace PfaffianDescent.PointAdaptedAffineCover
universe u

set_option backward.isDefEq.respectTransparency false in
/-- The principal-cover comparison has the same actual augmentation square
as the original point-adapted comparison, for a section supported at the point. -/
theorem principal_augmentation_square_of_supported_section
    {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    (hq : X.presheaf.germ U x hx q ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hf : X.presheaf.germ U x hx f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (M : X.Modules) (s : M.val.obj (op (⊤ : X.Opens)))
    (hsupport : ∀ V : X.Opens, x ∉ V →
      M.val.map (homOfLE (le_top : V ≤ ⊤)).op s = 0) :
    sectionRepresenterCechAugmentation X.ringCatSheaf (principalOpens U x q f) ⊤
        (isTerminalTop : IsTerminal (⊤ : X.Opens)) ≫
      (sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf (principalOpens U x q f) ⊤
        (isTerminalTop : IsTerminal (⊤ : X.Opens))).hom ≫
      sectionRepresenterAugmentation X.ringCatSheaf ⊤ M s =
    principalOnC₀ U x q f ≫ sectionRepresenterAugmentation X.ringCatSheaf U M
      (M.val.map (homOfLE (le_top : U ≤ ⊤)).op s) := by
  let σ := principalToAdaptedIndex U hU x hx q f hq hf
  let j : ∀ i, principalOpens U x q f i ⟶ opens U x (σ i) :=
    fun i => homOfLE (le_of_eq (principalToAdaptedIndex_opens U hU x hx q f hq hf i).symm)
  let a := principalToAdaptedChain U hU x hx q f hq hf
  let g := sectionRepresenterAugmentation X.ringCatSheaf ⊤ M s
  have he := sectionRepresenterCechRefinement_augmentation X.ringCatSheaf
    (opens U x) (principalOpens U x q f) σ j ⊤
      (isTerminalTop : IsTerminal (⊤ : X.Opens))
  let C₀ := (sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)).X 0
  let D₀ := (sectionRepresenterCechChain X.ringCatSheaf (opens U x)).X 0
  let a₀ : C₀ ⟶ D₀ := a.f 0
  let eNew : C₀ ⟶ sectionRepresenter X.ringCatSheaf ⊤ :=
    sectionRepresenterCechAugmentation X.ringCatSheaf (principalOpens U x q f) ⊤
      (isTerminalTop : IsTerminal (⊤ : X.Opens)) ≫
    (sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf (principalOpens U x q f) ⊤
      (isTerminalTop : IsTerminal (⊤ : X.Opens))).hom
  let eOld : D₀ ⟶ sectionRepresenter X.ringCatSheaf ⊤ :=
    sectionRepresenterCechAugmentation X.ringCatSheaf (opens U x) ⊤
      (isTerminalTop : IsTerminal (⊤ : X.Opens)) ≫
    (sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf (opens U x) ⊤
      (isTerminalTop : IsTerminal (⊤ : X.Opens))).hom
  let r : sectionRepresenter X.ringCatSheaf U ⟶ M :=
    sectionRepresenterAugmentation X.ringCatSheaf U M
      (M.val.map (homOfLE (le_top : U ≤ ⊤)).op s)
  have he₀ : eNew = a₀ ≫ eOld := he.symm
  have hold := augmentation_square_of_supported_section U x M s hsupport
  have hold₀ : eOld ≫ g = onC₀ U x ≫ r := by
    simpa only [eOld, g, r, Category.assoc] using hold
  have hzero₀ : a₀ ≫ onC₀ U x = principalOnC₀ U x q f :=
    principalOnC₀_refinement U hU x hx q f hq hf
  change eNew ≫ g = principalOnC₀ U x q f ≫ r
  calc
    eNew ≫ g = (a₀ ≫ eOld) ≫ g := congrArg (fun k => k ≫ g) he₀
    _ = a₀ ≫ (eOld ≫ g) := Category.assoc _ _ _
    _ = a₀ ≫ (onC₀ U x ≫ r) := congrArg (fun k => a₀ ≫ k) hold₀
    _ = (a₀ ≫ onC₀ U x) ≫ r := (Category.assoc _ _ _).symm
    _ = principalOnC₀ U x q f ≫ r := congrArg (fun k => k ≫ r) hzero₀

end PfaffianDescent.PointAdaptedAffineCover
