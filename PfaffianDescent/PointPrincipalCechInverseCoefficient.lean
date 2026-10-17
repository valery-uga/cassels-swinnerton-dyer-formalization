import PfaffianDescent.PointPrincipalCechStandardTriple

/-! # The actual second comparison component on the principal triple -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped nonZeroDivisors
namespace PfaffianDescent.PointAdaptedAffineCover
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
universe u

set_option backward.isDefEq.respectTransparency false in
/-- The actual second comparison map on the point/q/f triple is the positive
inverse-product scalar morphism, from its actual second differential square. -/
theorem principal_second_lift_triple_inverse_coefficient
    {X : Scheme.{u}} (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    (hqreg : X.presheaf.germ U x hx q ∈ (X.presheaf.stalk x)⁰)
    (hfreg : Ideal.Quotient.mk (Ideal.span {X.presheaf.germ U x hx q})
        (X.presheaf.germ U x hx f) ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ U x hx q})⁰)
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤)
    (L : ∀ i j : PrincipalIndex X x,
      sectionRepresenter X.ringCatSheaf (principalPairOpen U x q f i j) ⟶
        ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
    (uq : Γ(X, ∏ᶜ ![U, X.basicOpen q])) (uf : Γ(X, ∏ᶜ ![U, X.basicOpen f]))
    (huq : X.presheaf.map (Pi.π ![U, X.basicOpen q] 0).op q * uq = 1)
    (huf : X.presheaf.map (Pi.π ![U, X.basicOpen f] 0).op f * uf = 1)
    (hLq : L (Sum.inr none) (Sum.inl 0) =
      sectionRepresenterKoszulOverlapLift X.ringCatSheaf (Pi.π ![U, X.basicOpen q] 0) (-uq) 0)
    (hLf : L (Sum.inr none) (Sum.inl 1) =
      sectionRepresenterKoszulOverlapLift X.ringCatSheaf (Pi.π ![U, X.basicOpen f] 0) 0 (-uf))
    (hLzero : L (Sum.inl 0) (Sum.inl 1) = 0)
    (a₂ : (sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)).X 2 ⟶
      sectionRepresenter X.ringCatSheaf U)
    (h₂ : a₂ ≫ sectionRepresenterKoszulFirst X.ringCatSheaf U q f =
      (sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)).d 2 1 ≫
        principalAssembleFirstLift U x q f L) :
    let s : Fin 3 → PrincipalIndex X x := ![Sum.inr none, Sum.inl 0, Sum.inl 1]
    let W : X.Opens := ∏ᶜ fun k : Fin 3 => principalOpens U x q f (s k)
    let C := sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)
    let t : sectionRepresenter X.ringCatSheaf W ⟶ C.X 2 :=
      Sigma.ι (fun g : Fin 3 → PrincipalIndex X x =>
        sectionRepresenter X.ringCatSheaf (∏ᶜ fun k : Fin 3 => principalOpens U x q f (g k))) s
    let kq : W ⟶ ∏ᶜ ![U, X.basicOpen q] := principalTripleFaceToPair U x q f s 2
    let kf : W ⟶ ∏ᶜ ![U, X.basicOpen f] := principalTripleFaceToPair U x q f s 1
    t ≫ a₂ = sectionRepresenterOverlapScalar X.ringCatSheaf
      (kq ≫ Pi.π ![U, X.basicOpen q] 0)
      (X.presheaf.map kq.op uq * X.presheaf.map kf.op uf) := by
  dsimp only
  let s : Fin 3 → PrincipalIndex X x := ![Sum.inr none, Sum.inl 0, Sum.inl 1]
  let W : X.Opens := ∏ᶜ fun k : Fin 3 => principalOpens U x q f (s k)
  let kq : W ⟶ ∏ᶜ ![U, X.basicOpen q] := principalTripleFaceToPair U x q f s 2
  let kf : W ⟶ ∏ᶜ ![U, X.basicOpen f] := principalTripleFaceToPair U x q f s 1
  letI : Mono (sectionRepresenterKoszulFirst X.ringCatSheaf U q f) :=
    sectionRepresenterKoszulFirst_mono_of_regularPairAtPoint X U q f x hx hqreg hfreg haway
  apply (cancel_mono (sectionRepresenterKoszulFirst X.ringCatSheaf U q f)).1
  rw [Category.assoc, h₂]
  have hb := principalAssembleFirstLift_standard_triple_boundary U x q f L uq uf hLq hLf hLzero
  have hi := pointKoszul_restricted_first_lifts_boundary kq kf
    (Pi.π ![U, X.basicOpen q] 0) (Pi.π ![U, X.basicOpen f] 0) q f uq uf huq huf
  exact hb.trans hi.symm
end PfaffianDescent.PointAdaptedAffineCover
