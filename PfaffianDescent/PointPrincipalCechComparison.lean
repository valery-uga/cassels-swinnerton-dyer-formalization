import PfaffianDescent.PointPrincipalCechAssembly

/-! # The actual principal-cover comparison with prescribed first lifts -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped nonZeroDivisors
namespace PfaffianDescent.PointAdaptedAffineCover
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
universe u

set_option backward.isDefEq.respectTransparency false in
/-- Construct both positive-degree comparison maps, retaining the actual
inverse sections and all three prescribed first-lift components. -/
theorem exists_principal_standard_chain_comparison
    {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
    (U : X.Opens) (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    (hqreg : X.presheaf.germ U x hx q ∈ (X.presheaf.stalk x)⁰)
    (hfreg : Ideal.Quotient.mk (Ideal.span {X.presheaf.germ U x hx q})
        (X.presheaf.germ U x hx f) ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ U x hx q})⁰)
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤) :
    let D : PrincipalIndex X x := Sum.inr none
    let Q : PrincipalIndex X x := Sum.inl 0
    let F : PrincipalIndex X x := Sum.inl 1
    let Vq := principalPairOpen U x q f D Q
    let Vf := principalPairOpen U x q f D F
    let jq : Vq ⟶ U := Pi.π ![U, X.basicOpen q] 0
    let jf : Vf ⟶ U := Pi.π ![U, X.basicOpen f] 0
    let C := sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)
    ∃ (uq : Γ(X, Vq)) (uf : Γ(X, Vf))
      (L : ∀ i j : PrincipalIndex X x,
        sectionRepresenter X.ringCatSheaf (principalPairOpen U x q f i j) ⟶
          ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
      (a₂ : C.X 2 ⟶ sectionRepresenter X.ringCatSheaf U),
      X.presheaf.map jq.op q * uq = 1 ∧
      X.presheaf.map jf.op f * uf = 1 ∧
      (∀ i j, L i j ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
        principalPairBoundary U x q f i j) ∧
      L D Q = sectionRepresenterKoszulOverlapLift X.ringCatSheaf jq (-uq) 0 ∧
      L D F = sectionRepresenterKoszulOverlapLift X.ringCatSheaf jf 0 (-uf) ∧
      L Q F = 0 ∧
      a₂ ≫ sectionRepresenterKoszulFirst X.ringCatSheaf U q f =
        C.d 2 1 ≫ principalAssembleFirstLift U x q f L ∧
      C.d 3 2 ≫ a₂ = 0 := by
  dsimp only
  obtain ⟨uq, uf, L, huq, huf, hL, hLq, hLf, hLzero⟩ :=
    exists_principal_standard_pair_lifts U hU x q f haway
  let C := sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)
  let S := sectionRepresenterKoszulShortComplex X.ringCatSheaf U q f (Commute.all q f)
  have hex : S.Exact :=
    sectionRepresenterKoszul_exact_of_regularPairAtPoint X U q f x hx hqreg hfreg haway
  letI : Mono S.f :=
    sectionRepresenterKoszulFirst_mono_of_regularPairAtPoint X U q f x hx hqreg hfreg haway
  let a₁ := principalAssembleFirstLift U x q f L
  have h₁ : a₁ ≫ S.g = C.d 1 0 ≫ principalOnC₀ U x q f :=
    principalAssembleFirstLift_comp_last U x q f L hL
  have hz : (C.d 2 1 ≫ a₁) ≫ S.g = 0 := by
    rw [Category.assoc, h₁, ← Category.assoc, C.d_comp_d, zero_comp]
  let a₂ : C.X 2 ⟶ S.X₁ := hex.fIsKernel.lift (KernelFork.ofι (C.d 2 1 ≫ a₁) hz)
  have h₂ : a₂ ≫ S.f = C.d 2 1 ≫ a₁ :=
    hex.fIsKernel.fac (KernelFork.ofι (C.d 2 1 ≫ a₁) hz) WalkingParallelPair.zero
  refine ⟨uq, uf, L, a₂, huq, huf, hL, hLq, hLf, hLzero, h₂, ?_⟩
  apply (cancel_mono S.f).1
  rw [Category.assoc, h₂, ← Category.assoc, C.d_comp_d, zero_comp, zero_comp]
end PfaffianDescent.PointAdaptedAffineCover
