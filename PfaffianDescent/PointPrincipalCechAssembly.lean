import PfaffianDescent.PointPrincipalCechStandardLifts

/-! # Assembly of the prescribed principal-cover first lifts -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace PfaffianDescent.PointAdaptedAffineCover
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
universe u
variable {X : Scheme.{u}}

def principalPairProjection (U : X.Opens) (x : X) (q f : Γ(X, U))
    (s : Fin 2 → PrincipalIndex X x) :
    (∏ᶜ fun k : Fin 2 => principalOpens U x q f (s k)) ⟶
      principalPairOpen U x q f (s 0) (s 1) :=
  Pi.lift (fun k : Fin 2 => homOfLE (by
    fin_cases k
    · exact (Pi.π (fun k : Fin 2 => principalOpens U x q f (s k)) 0).le
    · exact (Pi.π (fun k : Fin 2 => principalOpens U x q f (s k)) 1).le))

def principalOnC₀ (U : X.Opens) (x : X) (q f : Γ(X, U)) :
    (sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)).X 0 ⟶
      sectionRepresenter X.ringCatSheaf U :=
  sectionRepresenterCechVertexMap X.ringCatSheaf (principalOpens U x q f)
    (sectionRepresenter X.ringCatSheaf U) (principalVertexMap U x q f)

def principalAssembleFirstLift (U : X.Opens) (x : X) (q f : Γ(X, U))
    (L : ∀ i j : PrincipalIndex X x,
      sectionRepresenter X.ringCatSheaf (principalPairOpen U x q f i j) ⟶
        ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U) :
    (sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)).X 1 ⟶
      ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U :=
  Sigma.desc (fun s : Fin 2 → PrincipalIndex X x =>
    (sectionRepresenterFunctor X.ringCatSheaf).map (principalPairProjection U x q f s) ≫
      L (s 0) (s 1))

set_option backward.isDefEq.respectTransparency false in
/-- The assembled first lift has the literal chosen ordered-overlap components. -/
theorem principalAssembleFirstLift_component
    (U : X.Opens) (x : X) (q f : Γ(X, U))
    (L : ∀ i j : PrincipalIndex X x,
      sectionRepresenter X.ringCatSheaf (principalPairOpen U x q f i j) ⟶
        ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
    (s : Fin 2 → PrincipalIndex X x) :
    Sigma.ι (fun g : Fin 2 → PrincipalIndex X x =>
        sectionRepresenter X.ringCatSheaf (∏ᶜ fun k : Fin 2 => principalOpens U x q f (g k))) s ≫
      principalAssembleFirstLift U x q f L =
      (sectionRepresenterFunctor X.ringCatSheaf).map (principalPairProjection U x q f s) ≫
        L (s 0) (s 1) := by
  exact Sigma.ι_desc _ _

set_option backward.isDefEq.respectTransparency false in
/-- The local first-lift squares assemble into the actual Cech differential square. -/
theorem principalAssembleFirstLift_comp_last
    (U : X.Opens) (x : X) (q f : Γ(X, U))
    (L : ∀ i j : PrincipalIndex X x,
      sectionRepresenter X.ringCatSheaf (principalPairOpen U x q f i j) ⟶
        ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
    (hL : ∀ i j, L i j ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
      principalPairBoundary U x q f i j) :
    principalAssembleFirstLift U x q f L ≫
        sectionRepresenterKoszulLast X.ringCatSheaf U q f =
      (sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)).d 1 0 ≫
        principalOnC₀ U x q f := by
  apply Sigma.hom_ext
  intro s
  change Sigma.ι (fun g : Fin 2 → PrincipalIndex X x =>
      sectionRepresenter X.ringCatSheaf (∏ᶜ fun k : Fin 2 => principalOpens U x q f (g k))) s ≫
      (principalAssembleFirstLift U x q f L ≫
        sectionRepresenterKoszulLast X.ringCatSheaf U q f) =
    Sigma.ι (fun g : Fin 2 → PrincipalIndex X x =>
      sectionRepresenter X.ringCatSheaf (∏ᶜ fun k : Fin 2 => principalOpens U x q f (g k))) s ≫
      ((sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)).d 1 0 ≫
        principalOnC₀ U x q f)
  rw [← Category.assoc, principalAssembleFirstLift_component, Category.assoc, hL]
  change (sectionRepresenterFunctor X.ringCatSheaf).map (principalPairProjection U x q f s) ≫
      principalPairBoundary U x q f (s 0) (s 1) =
    Sigma.ι (fun g : Fin 2 → PrincipalIndex X x =>
      sectionRepresenter X.ringCatSheaf (∏ᶜ fun k : Fin 2 => principalOpens U x q f (g k))) s ≫
      (sectionRepresenterCechChain X.ringCatSheaf (principalOpens U x q f)).d 1 0 ≫
        sectionRepresenterCechVertexMap X.ringCatSheaf (principalOpens U x q f)
          (sectionRepresenter X.ringCatSheaf U) (principalVertexMap U x q f)
  rw [sectionRepresenterCechVertexMap_boundary_component]
  have he₀ : principalPairProjection U x q f s ≫
      Pi.π ![principalOpens U x q f (s 0), principalOpens U x q f (s 1)] 0 =
      Pi.π (fun k : Fin 2 => principalOpens U x q f (s k)) 0 := Subsingleton.elim _ _
  have he₁ : principalPairProjection U x q f s ≫
      Pi.π ![principalOpens U x q f (s 0), principalOpens U x q f (s 1)] 1 =
      Pi.π (fun k : Fin 2 => principalOpens U x q f (s k)) 1 := Subsingleton.elim _ _
  change (sectionRepresenterFunctor X.ringCatSheaf).map (principalPairProjection U x q f s) ≫
      ((sectionRepresenterFunctor X.ringCatSheaf).map
          (Pi.π ![principalOpens U x q f (s 0), principalOpens U x q f (s 1)] 1) ≫
          principalVertexMap U x q f (s 1) -
        (sectionRepresenterFunctor X.ringCatSheaf).map
          (Pi.π ![principalOpens U x q f (s 0), principalOpens U x q f (s 1)] 0) ≫
          principalVertexMap U x q f (s 0)) = _
  rw [Preadditive.comp_sub, ← Category.assoc, ← Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, he₁, he₀]
end PfaffianDescent.PointAdaptedAffineCover
