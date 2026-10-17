import PfaffianDescent.PointPrincipalCechTripleBoundary

/-! # The standard signed boundary on the actual principal triple -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace PfaffianDescent.PointAdaptedAffineCover
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
universe u

private theorem sum_three_alternating {A : Type u} [AddCommGroup A] (r : Fin 3 → A) :
    (∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • r i) = r 0 - r 1 + r 2 := by
  simp [Fin.sum_univ_three, sub_eq_add_neg]

set_option backward.isDefEq.respectTransparency false in
/-- On the actual point/q/f triple, the assembled first lift has the standard
signed boundary of the two actual restricted inverse lifts. -/
theorem principalAssembleFirstLift_standard_triple_boundary
    {X : Scheme.{u}} (U : X.Opens) (x : X) (q f : Γ(X, U))
    (L : ∀ i j : PrincipalIndex X x,
      sectionRepresenter X.ringCatSheaf (principalPairOpen U x q f i j) ⟶
        ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
    (uq : Γ(X, ∏ᶜ ![U, X.basicOpen q])) (uf : Γ(X, ∏ᶜ ![U, X.basicOpen f]))
    (hLq : L (Sum.inr none) (Sum.inl 0) =
      sectionRepresenterKoszulOverlapLift X.ringCatSheaf (Pi.π ![U, X.basicOpen q] 0) (-uq) 0)
    (hLf : L (Sum.inr none) (Sum.inl 1) =
      sectionRepresenterKoszulOverlapLift X.ringCatSheaf (Pi.π ![U, X.basicOpen f] 0) 0 (-uf))
    (hLzero : L (Sum.inl 0) (Sum.inl 1) = 0) :
    let s : Fin 3 → PrincipalIndex X x := ![Sum.inr none, Sum.inl 0, Sum.inl 1]
    let W : X.Opens := ∏ᶜ fun k : Fin 3 => principalOpens U x q f (s k)
    let C := sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)
    let t : sectionRepresenter X.ringCatSheaf W ⟶ C.X 2 :=
      Sigma.ι (fun g : Fin 3 → PrincipalIndex X x =>
        sectionRepresenter X.ringCatSheaf (∏ᶜ fun k : Fin 3 => principalOpens U x q f (g k))) s
    t ≫ C.d 2 1 ≫ principalAssembleFirstLift U x q f L =
      0 - ((sectionRepresenterFunctor X.ringCatSheaf).map
          (principalTripleFaceToPair U x q f s 1) ≫
        sectionRepresenterKoszulOverlapLift X.ringCatSheaf (Pi.π ![U, X.basicOpen f] 0) 0 (-uf) :
          sectionRepresenter X.ringCatSheaf W ⟶ ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U) +
        ((sectionRepresenterFunctor X.ringCatSheaf).map
          (principalTripleFaceToPair U x q f s 2) ≫
        sectionRepresenterKoszulOverlapLift X.ringCatSheaf (Pi.π ![U, X.basicOpen q] 0) (-uq) 0 :
          sectionRepresenter X.ringCatSheaf W ⟶ ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U) := by
  dsimp only
  let s : Fin 3 → PrincipalIndex X x := ![Sum.inr none, Sum.inl 0, Sum.inl 1]
  let W : X.Opens := ∏ᶜ fun k : Fin 3 => principalOpens U x q f (s k)
  let C := sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)
  let t : sectionRepresenter X.ringCatSheaf W ⟶ C.X 2 :=
    Sigma.ι (fun g : Fin 3 → PrincipalIndex X x =>
      sectionRepresenter X.ringCatSheaf (∏ᶜ fun k : Fin 3 => principalOpens U x q f (g k))) s
  let r : Fin 3 → (sectionRepresenter X.ringCatSheaf W ⟶
      ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U) :=
    fun i => (sectionRepresenterFunctor X.ringCatSheaf).map
      (principalTripleFaceToPair U x q f s i) ≫ L (s (i.succAbove 0)) (s (i.succAbove 1))
  have h := principalAssembleFirstLift_triple_boundary U x q f L s
  change t ≫ C.d 2 1 ≫ principalAssembleFirstLift U x q f L =
    ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • r i at h
  have hr0 : r 0 = 0 := by
    change (sectionRepresenterFunctor X.ringCatSheaf).map
      (principalTripleFaceToPair U x q f s 0) ≫ L (Sum.inl 0) (Sum.inl 1) = 0
    rw [hLzero, comp_zero]
  have hr1 : r 1 =
      ((sectionRepresenterFunctor X.ringCatSheaf).map
        (principalTripleFaceToPair U x q f s 1) ≫
        sectionRepresenterKoszulOverlapLift X.ringCatSheaf (Pi.π ![U, X.basicOpen f] 0) 0 (-uf) :
        sectionRepresenter X.ringCatSheaf W ⟶ ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U) := by
    change (sectionRepresenterFunctor X.ringCatSheaf).map
      (principalTripleFaceToPair U x q f s 1) ≫ L (Sum.inr none) (Sum.inl 1) = _
    rw [hLf]
  have hr2 : r 2 =
      ((sectionRepresenterFunctor X.ringCatSheaf).map
        (principalTripleFaceToPair U x q f s 2) ≫
        sectionRepresenterKoszulOverlapLift X.ringCatSheaf (Pi.π ![U, X.basicOpen q] 0) (-uq) 0 :
        sectionRepresenter X.ringCatSheaf W ⟶ ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U) := by
    change (sectionRepresenterFunctor X.ringCatSheaf).map
      (principalTripleFaceToPair U x q f s 2) ≫ L (Sum.inr none) (Sum.inl 0) = _
    rw [hLq]
  rw [sum_three_alternating r] at h
  rw [hr0, hr1, hr2] at h
  exact h

end PfaffianDescent.PointAdaptedAffineCover
