import PfaffianDescent.SectionRepresenterFormalCoproductOver
import PfaffianDescent.SectionRepresenterCechSplit
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# Exactness of the section-representer Cech chain for a cover

After restriction to a member of the cover, the Cech nerve is split by the
diagonal of that member.  Restriction functors are exact and jointly
conservative, so this local contraction proves global exactness in every
positive chain degree.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace PfaffianDescent

universe u

variable {C : Type u} [SmallCategory C] [HasFiniteLimits C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ Y, HasSheafify (J.over Y) AddCommGrpCat.{u}]
variable [∀ Y, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The alternating section-representer Cech chain of a covering family is
exact in every positive degree. -/
lemma sectionRepresenterCechChain_exactAt_succ_of_coversTop
    {ι : Type u} (U : ι → C) (hU : J.CoversTop U) (n : ℕ) :
    (sectionRepresenterCechChain R U).ExactAt (n + 1) := by
  let F : ∀ i, SheafOfModules.{u} R ⥤ SheafOfModules.{u} (R.over (U i)) :=
    fun i => SheafOfModules.overFunctor R (U i)
  let hF : JointlyReflectIsomorphisms F :=
    SheafOfModules.overFunctors_jointlyReflectIsomorphisms U hU
  letI : ∀ i, (F i).IsLeftAdjoint := fun i => by
    dsimp [F]
    exact (SheafOfModules.overPushforwardOverAdj (R := R) (U i)).isLeftAdjoint
  letI : ∀ i, PreservesFiniteLimits (F i) := fun i => by
    dsimp [F]
    exact SheafOfModules.overFunctor_preservesFiniteLimits R (U i)
  letI : ∀ i, PreservesFiniteColimits (F i) := fun _ => by
    infer_instance
  letI : ∀ i, (F i).Additive := fun i => by
    dsimp [F]
    exact overFunctorAdditive R (U i)
  rw [hF.exactAt_iff]
  intro i
  letI : HasFiniteProducts (Over (U i)) :=
    CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
  let T : Over (U i) := Over.mk (𝟙 (U i))
  let hT : IsTerminal T := Over.mkIdTerminal
  let d : T ⟶ (Over.star (U i)).obj (U i) :=
    (Over.forgetAdjStar (U i)).unit.app T
  have hlocal :
      (sectionRepresenterCechChain (R.over (U i))
        (fun j => (Over.star (U i)).obj (U j))).ExactAt (n + 1) :=
    sectionRepresenterCechChain_exactAt_succ_of_split
      (R.over (U i)) (fun j => (Over.star (U i)).obj (U j)) T hT d n
  exact hlocal.of_iso (overSectionRepresenterCechChainIso R (U i) U)

end PfaffianDescent
