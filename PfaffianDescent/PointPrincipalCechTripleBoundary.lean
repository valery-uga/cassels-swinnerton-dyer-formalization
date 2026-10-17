import PfaffianDescent.PointPrincipalCechComparison
import PfaffianDescent.SectionRepresenterCechDegreeOneBoundary

/-! # Actual triple components of the assembled principal first lift -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Simplicial
namespace PfaffianDescent.PointAdaptedAffineCover
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
universe u
variable {X : Scheme.{u}}

def principalTripleFaceToPair (U : X.Opens) (x : X) (q f : Γ(X, U))
    (s : Fin 3 → PrincipalIndex X x) (i : Fin 3) :
    (∏ᶜ fun k : Fin 3 => principalOpens U x q f (s k)) ⟶
      principalPairOpen U x q f (s (i.succAbove 0)) (s (i.succAbove 1)) :=
  Pi.lift (fun k : Fin 2 => homOfLE (by
    fin_cases k
    · exact (Pi.π (fun k : Fin 3 => principalOpens U x q f (s k)) (i.succAbove 0)).le
    · exact (Pi.π (fun k : Fin 3 => principalOpens U x q f (s k)) (i.succAbove 1)).le))

set_option backward.isDefEq.respectTransparency false in
/-- Each actual triple face restricts exactly the corresponding chosen pair lift. -/
theorem principalAssembleFirstLift_face_component
    (U : X.Opens) (x : X) (q f : Γ(X, U))
    (L : ∀ i j : PrincipalIndex X x,
      sectionRepresenter X.ringCatSheaf (principalPairOpen U x q f i j) ⟶
        ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
    (s : Fin 3 → PrincipalIndex X x) (i : Fin 3) :
    Sigma.ι (fun g : Fin 3 → PrincipalIndex X x =>
        sectionRepresenter X.ringCatSheaf (∏ᶜ fun k : Fin 3 => principalOpens U x q f (g k))) s ≫
      (sectionRepresenterCechSimplicial X.ringCatSheaf (principalOpens U x q f)).δ i ≫
        principalAssembleFirstLift U x q f L =
      (sectionRepresenterFunctor X.ringCatSheaf).map (principalTripleFaceToPair U x q f s i) ≫
        L (s (i.succAbove 0)) (s (i.succAbove 1)) := by
  rw [sectionRepresenterCech_degreeOne_face_component]
  change (sectionRepresenterFunctor X.ringCatSheaf).map
      (Pi.lift (fun k : Fin 2 =>
        Pi.π (fun a : Fin 3 => principalOpens U x q f (s a)) (i.succAbove k))) ≫
      (Sigma.ι (fun g : Fin 2 → PrincipalIndex X x =>
        sectionRepresenter X.ringCatSheaf (∏ᶜ fun k : Fin 2 => principalOpens U x q f (g k)))
          (fun k => s (i.succAbove k)) ≫ principalAssembleFirstLift U x q f L) = _
  rw [principalAssembleFirstLift_component, ← Category.assoc, ← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The actual second differential of the assembled first lift is the signed
sum of its three chosen pair lifts, with the actual triple inclusion maps. -/
theorem principalAssembleFirstLift_triple_boundary
    (U : X.Opens) (x : X) (q f : Γ(X, U))
    (L : ∀ i j : PrincipalIndex X x,
      sectionRepresenter X.ringCatSheaf (principalPairOpen U x q f i j) ⟶
        ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
    (s : Fin 3 → PrincipalIndex X x) :
    Sigma.ι (fun g : Fin 3 → PrincipalIndex X x =>
        sectionRepresenter X.ringCatSheaf (∏ᶜ fun k : Fin 3 => principalOpens U x q f (g k))) s ≫
      (sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)).d 2 1 ≫
        principalAssembleFirstLift U x q f L =
      ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) •
        ((sectionRepresenterFunctor X.ringCatSheaf).map (principalTripleFaceToPair U x q f s i) ≫
          L (s (i.succAbove 0)) (s (i.succAbove 1))) := by
  have h := sectionRepresenterCech_degreeOne_boundary_component X.ringCatSheaf
    (principalOpens U x q f) (⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
      (principalAssembleFirstLift U x q f L) s
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun v => (-1 : ℤ) ^ (i : ℕ) • v)
    ((sectionRepresenterCech_degreeOne_face_component X.ringCatSheaf
      (principalOpens U x q f) (⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
        (principalAssembleFirstLift U x q f L) s i).symm.trans
      (principalAssembleFirstLift_face_component U x q f L s i))
end PfaffianDescent.PointAdaptedAffineCover
