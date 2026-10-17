import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! Finiteness over a field descends from any extension field by finite fibers. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- A quasi-compact finite-type scheme over a field is finite if its base
change to any extension field is finite. The proof uses surjectivity of the
field base change and the finite-fiber criterion for quasi-finiteness. -/
theorem isFinite_of_isFinite_fieldBaseChange
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [QuasiCompact f] [LocallyOfFiniteType f]
    [IsFinite (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap K L))))] :
    IsFinite f := by
  let g : Spec (.of L) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  haveI : Surjective g := by
    constructor
    intro x
    exact ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩
  haveI : Surjective (pullback.fst f g) := inferInstance
  let P : Scheme.{u} := pullback f g
  have hsource : Finite P := by
    have hpre := (pullback.snd f g).finite_preimage_singleton
      (IsLocalRing.closedPoint L)
    have heq : (pullback.snd f g) ⁻¹' {IsLocalRing.closedPoint L} =
        (Set.univ : Set P) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    exact Finite.of_finite_univ (heq ▸ hpre)
  letI : Finite P := hsource
  haveI : Finite X :=
    Finite.of_surjective (pullback.fst f g) (pullback.fst f g).surjective
  haveI : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_finite_preimage_singleton f (fun _ => Set.toFinite _)
  exact IsFinite.of_locallyQuasiFinite f

end PfaffianDescent
