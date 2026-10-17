import PfaffianDescent.PointAdaptedCechExt
import PfaffianDescent.SectionRepresenterCechRefinement

/-!
# Common refinements of the point-adapted affine cover

Intersecting the actual point-adapted cover with a second affine cover
gives a covering family and explicit refinement maps to both covers.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PfaffianDescent.PointAdaptedAffineCover

universe u

variable {X : Scheme.{u}} {κ : Type u}

/-- Intersections of the actual adapted cover with a supplied second cover. -/
def commonOpens (U : X.Opens) (x : X) (V : κ → X.Opens) :
    Index X x × κ → X.Opens := fun a => opens U x a.1 ⊓ V a.2

/-- Both covering equalities imply that the actual intersection family covers. -/
theorem commonOpens_coversTop (U : X.Opens) (x : X) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set X)) (V : κ → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V) :
    (Opens.grothendieckTopology X).CoversTop (commonOpens U x V) := by
  apply (Opens.coversTop_iff X _).mpr
  have hVtop := (Opens.coversTop_iff X V).mp hV
  have hUtop := covers U x hx hxclosed
  apply top_unique
  intro z hz
  have hzU : z ∈ ⨆ a, opens U x a := by rw [hUtop]; trivial
  have hzV : z ∈ ⨆ b, V b := by rw [hVtop]; trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hzU
  obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp hzV
  exact (le_iSup (commonOpens U x V) (a, b)) ⟨ha, hb⟩

/-- The common refinement consists of affine opens on a scheme with affine
diagonal, as required for the local Koszul and Cech calculations. -/
theorem commonOpens_isAffineOpen
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (U : X.Opens) (hU : IsAffineOpen U) (x : X)
    (V : κ → X.Opens) (hV : ∀ b, IsAffineOpen (V b)) (a : Index X x × κ) :
    IsAffineOpen (commonOpens U x V a) :=
  (isAffineOpen U hU x a.1).inf (hV a.2)

/-- The actual chain refinement to the point-adapted cover. -/
def commonToPointChain (U : X.Opens) (x : X) (V : κ → X.Opens) :
    sectionRepresenterCechChain X.ringCatSheaf (commonOpens U x V) ⟶
      sectionRepresenterCechChain X.ringCatSheaf (opens U x) :=
  sectionRepresenterCechRefinement X.ringCatSheaf (opens U x) (commonOpens U x V)
    Prod.fst (fun _ => homOfLE inf_le_left)

/-- The actual chain refinement to the second cover. -/
def commonToOtherChain (U : X.Opens) (x : X) (V : κ → X.Opens) :
    sectionRepresenterCechChain X.ringCatSheaf (commonOpens U x V) ⟶
      sectionRepresenterCechChain X.ringCatSheaf V :=
  sectionRepresenterCechRefinement X.ringCatSheaf V (commonOpens U x V)
    Prod.snd (fun _ => homOfLE inf_le_right)

end PfaffianDescent.PointAdaptedAffineCover
