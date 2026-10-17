import PfaffianDescent.PointPrincipalCechInverseCoefficient

/-! # Constructed principal-cover comparison with computed residue component -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped nonZeroDivisors
namespace PfaffianDescent.PointAdaptedAffineCover
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
universe u

set_option backward.isDefEq.respectTransparency false in
/-- Construct the comparison and compute its principal triple component.
The inverse sections, first/second squares, and cocycle equation are all
proved, rather than supplied as comparison or normalization hypotheses. -/
theorem exists_principal_normalized_chain_comparison
    {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
    (U : X.Opens) (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    (hqreg : X.presheaf.germ U x hx q ∈ (X.presheaf.stalk x)⁰)
    (hfreg : Ideal.Quotient.mk (Ideal.span {X.presheaf.germ U x hx q})
        (X.presheaf.germ U x hx f) ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ U x hx q})⁰)
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤) :
    let s : Fin 3 → PrincipalIndex X x := ![Sum.inr none, Sum.inl 0, Sum.inl 1]
    let W : X.Opens := ∏ᶜ fun k : Fin 3 => principalOpens U x q f (s k)
    let Vq : X.Opens := ∏ᶜ ![U, X.basicOpen q]
    let Vf : X.Opens := ∏ᶜ ![U, X.basicOpen f]
    let jq : Vq ⟶ U := Pi.π ![U, X.basicOpen q] 0
    let jf : Vf ⟶ U := Pi.π ![U, X.basicOpen f] 0
    let C := sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)
    let t : sectionRepresenter X.ringCatSheaf W ⟶ C.X 2 :=
      Sigma.ι (fun g : Fin 3 → PrincipalIndex X x =>
        sectionRepresenter X.ringCatSheaf (∏ᶜ fun k : Fin 3 => principalOpens U x q f (g k))) s
    let kq : W ⟶ Vq := principalTripleFaceToPair U x q f s 2
    let kf : W ⟶ Vf := principalTripleFaceToPair U x q f s 1
    ∃ (uq : Γ(X, Vq)) (uf : Γ(X, Vf))
      (L : ∀ i j : PrincipalIndex X x,
        sectionRepresenter X.ringCatSheaf (principalPairOpen U x q f i j) ⟶
          ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
      (a₂ : C.X 2 ⟶ sectionRepresenter X.ringCatSheaf U),
      X.presheaf.map jq.op q * uq = 1 ∧
      X.presheaf.map jf.op f * uf = 1 ∧
      principalAssembleFirstLift U x q f L ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
        C.d 1 0 ≫ principalOnC₀ U x q f ∧
      a₂ ≫ sectionRepresenterKoszulFirst X.ringCatSheaf U q f =
        C.d 2 1 ≫ principalAssembleFirstLift U x q f L ∧
      C.d 3 2 ≫ a₂ = 0 ∧
      t ≫ a₂ = sectionRepresenterOverlapScalar X.ringCatSheaf (kq ≫ jq)
        (X.presheaf.map kq.op uq * X.presheaf.map kf.op uf) := by
  dsimp only
  obtain ⟨uq, uf, L, a₂, huq, huf, hL, hLq, hLf, hLzero, h₂, h₃⟩ :=
    exists_principal_standard_chain_comparison U hU x hx q f hqreg hfreg haway
  refine ⟨uq, uf, L, a₂, huq, huf,
    principalAssembleFirstLift_comp_last U x q f L hL, h₂, h₃, ?_⟩
  exact principal_second_lift_triple_inverse_coefficient U x hx q f hqreg hfreg haway
    L uq uf huq huf hLq hLf hLzero a₂ h₂
end PfaffianDescent.PointAdaptedAffineCover
