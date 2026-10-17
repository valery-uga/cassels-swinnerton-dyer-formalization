import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationFiber
import PfaffianDescent.AffineFreeModuleBaseChange

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual native affine Gamma at ANY actual field-valued point is
free of rank two, derived from the actual Serre rank-two affine cover. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_serreFiber_exists_nativeLinearEquiv
    {E : Type u} [Field E] {X : Scheme.{u}} {M : X.Modules}
    (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (r : Spec (CommRingCat.of E) ⟶ X) :
    Nonempty ((moduleSpecΓFunctor (R := CommRingCat.of E)).obj
      ((Scheme.Modules.pullback r).obj (show X.Modules from e.E)) ≃ₗ[E]
      (ULift.{u} (Fin 2) →₀ E)) := by
  obtain ⟨t⟩ := cubicClosedPointSerreDegreeThreeEvaluationFiber_exists_freeIso e C r
  exact ⟨(specModuleSectionsLinearEquivOfFreeIso E (ULift.{u} (Fin 2)) _ t).symm⟩

/-- The literal E-linear Gamma of the actual Serre point pullback has
finrank two; no residue-degree or fibre-coordinate certificate is an input. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_serreFiber_native_finrank_two
    {E : Type u} [Field E] {X : Scheme.{u}} {M : X.Modules}
    (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (r : Spec (CommRingCat.of E) ⟶ X) :
    Module.finrank E ((moduleSpecΓFunctor (R := CommRingCat.of E)).obj
      ((Scheme.Modules.pullback r).obj (show X.Modules from e.E))) = 2 := by
  obtain ⟨q⟩ := cubicClosedPointSerreSurfaceJetCotangent_serreFiber_exists_nativeLinearEquiv e C r
  rw [q.finrank_eq, Module.finrank_finsupp]
  simp

/-- Three actual point pullbacks have a six-dimensional ACTUAL native
Gamma product, including r_i=Spec(alpha_i)≫the original field-point immersion. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_serreThreeFiber_native_finrank_six
    {E : Type u} [Field E] {X : Scheme.{u}} {M : X.Modules}
    (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (r : Fin 3 → (Spec (CommRingCat.of E) ⟶ X)) :
    Module.finrank E (∀ i : Fin 3,
      (moduleSpecΓFunctor (R := CommRingCat.of E)).obj
        ((Scheme.Modules.pullback (r i)).obj (show X.Modules from e.E))) = 6 := by
  letI (i : Fin 3) : Module.Finite E
      ((moduleSpecΓFunctor (R := CommRingCat.of E)).obj
        ((Scheme.Modules.pullback (r i)).obj (show X.Modules from e.E))) :=
    Module.finite_of_finrank_pos (by
      rw [cubicClosedPointSerreSurfaceJetCotangent_serreFiber_native_finrank_two e C (r i)]
      decide)
  rw [Module.finrank_pi_fintype]
  simp only [cubicClosedPointSerreSurfaceJetCotangent_serreFiber_native_finrank_two e C]
  decide

end PfaffianDescent
