import PfaffianDescent.ClosedImmersionIdealBaseChangeSourceIso
import PfaffianDescent.ClosedImmersionIdealBaseChangeOpenCover

/-!
# Gluing ideal base change over an open cover of the parameter source

For a map into a parameter scheme, pull back an open cover of the parameter
source to the ambient family. The resulting pieces are canonically the
fibres over the original cover members, and ideal base change glues from
those pieces.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem isIso_closedImmersionIdealBaseChangeHom_of_baseOpenCover
    {X Y S W : Scheme.{u}}
    (p : X ⟶ Y) (f : S ⟶ Y) (i : W ⟶ X)
    [IsClosedImmersion i]
    (𝒰 : S.OpenCover)
    (h : ∀ a : 𝒰.I₀,
      IsIso (closedImmersionIdealBaseChangeHom
        (pullback.fst p (𝒰.f a ≫ f)) i)) :
    IsIso (closedImmersionIdealBaseChangeHom (pullback.fst p f) i) := by
  let 𝒱 : (pullback p f).OpenCover := 𝒰.pullback₁ (pullback.snd p f)
  apply isIso_closedImmersionIdealBaseChangeHom_of_openCover_comp_isIso
    (pullback.fst p f) i 𝒱
  intro a
  let e := pullbackLeftPullbackSndIso p f (𝒰.f a)
  have he : e.hom ≫ pullback.fst p (𝒰.f a ≫ f) =
      𝒱.f a ≫ pullback.fst p f := by
    change e.hom ≫ pullback.fst p (𝒰.f a ≫ f) =
      pullback.fst (pullback.snd p f) (𝒰.f a) ≫ pullback.fst p f
    exact pullbackLeftPullbackSndIso_hom_fst p f (𝒰.f a)
  have he' : e.inv ≫ (𝒱.f a ≫ pullback.fst p f) =
      pullback.fst p (𝒰.f a ≫ f) := by
    calc
      _ = e.inv ≫ (e.hom ≫ pullback.fst p (𝒰.f a ≫ f)) :=
        congrArg (e.inv ≫ ·) he.symm
      _ = (e.inv ≫ e.hom) ≫ pullback.fst p (𝒰.f a ≫ f) :=
        (Category.assoc _ _ _).symm
      _ = _ := by rw [e.inv_hom_id, Category.id_comp]
  have hcomp : IsIso (closedImmersionIdealBaseChangeHom
      (e.symm.hom ≫ (𝒱.f a ≫ pullback.fst p f)) i) := by
    change IsIso (closedImmersionIdealBaseChangeHom
      (e.inv ≫ (𝒱.f a ≫ pullback.fst p f)) i)
    rw [he']
    exact h a
  letI : IsIso (closedImmersionIdealBaseChangeHom
      (e.symm.hom ≫ (𝒱.f a ≫ pullback.fst p f)) i) := hcomp
  exact isIso_closedImmersionIdealBaseChangeHom_of_sourceIso e.symm
    (𝒱.f a ≫ pullback.fst p f) i

end PfaffianDescent
