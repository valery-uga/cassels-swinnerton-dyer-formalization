import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualAffineMarkedFieldSeed
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualEtaleOpenTransport

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_chartMarkedSeed_of_field_stalks
    {K : Type u} [Field K] {A B Z Y : Scheme.{u}} [IsAffine A] [IsAffine B]
    (g : Z ⟶ Y) (j : Y ⟶ Z)
    (a : A ⟶ Z) [IsOpenImmersion a] (b : B ⟶ Y) [IsOpenImmersion b]
    (g' : A ⟶ B) [LocallyOfFinitePresentation g']
    (j' : B ⟶ A) (hj' : j' ≫ g' = 𝟙 B)
    (hg : a ≫ g = g' ≫ b) (hj : j' ≫ a = b ≫ j)
    (i : Spec (.of K) ⟶ B) [IsClosedImmersion i]
    (hfield : ∀ z : (pullback g' i : Scheme), IsField ((pullback g' i).presheaf.stalk z))
    (c : Spec (.of K))
    [IsNoetherianRing (A.presheaf.stalk (j' (i c)))] :
    b (i c) ∈ cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen g j := by
  have hseed := cubicClosedPointSerreFiniteZeroResidual_affineMarkedSeed_of_field_stalks g' j' hj' i hfield c
  change j' (i c) ∈ cubicClosedPointSerreFiniteZeroResidual_etaleOpen g' at hseed
  have hpost := cubicClosedPointSerreFiniteZeroResidual_etaleOpen_mem_postcomp
    g' b (j' (i c)) hseed
  rw [← hg] at hpost
  have hglobal := cubicClosedPointSerreFiniteZeroResidual_etaleOpen_mem_under_openImmersion
    a g (j' (i c)) hpost
  change j (b (i c)) ∈ cubicClosedPointSerreFiniteZeroResidual_etaleOpen g
  have he : a (j' (i c)) = j (b (i c)) :=
    congrArg (fun f : B ⟶ Z => f (i c)) hj
  exact he ▸ hglobal

theorem cubicClosedPointSerreFiniteZeroResidual_chartThreeMarkedSeed_of_field_stalks
    {K : Type u} [Field K] {A B Z Y : Scheme.{u}} [IsAffine A] [IsAffine B]
    (g : Z ⟶ Y) (j : Fin 3 → (Y ⟶ Z))
    (a : A ⟶ Z) [IsOpenImmersion a] (b : B ⟶ Y) [IsOpenImmersion b]
    (g' : A ⟶ B) [LocallyOfFinitePresentation g']
    (j' : Fin 3 → (B ⟶ A)) (hj' : ∀ n, j' n ≫ g' = 𝟙 B)
    (hg : a ≫ g = g' ≫ b) (hj : ∀ n, j' n ≫ a = b ≫ j n)
    (i : Spec (.of K) ⟶ B) [IsClosedImmersion i]
    (hfield : ∀ z : (pullback g' i : Scheme), IsField ((pullback g' i).presheaf.stalk z))
    (c : Spec (.of K))
    [∀ n, IsNoetherianRing (A.presheaf.stalk (j' n (i c)))] :
    b (i c) ∈ cubicClosedPointSerreFiniteZeroResidual_threeMarkedSectionOpen g j := by
  change b (i c) ∈ ⨅ n : Fin 3, cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen g (j n)
  rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  intro n
  exact cubicClosedPointSerreFiniteZeroResidual_chartMarkedSeed_of_field_stalks g (j n) a b g' (j' n)
    (hj' n) hg (hj n) i hfield c

end PfaffianDescent
