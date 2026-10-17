import PfaffianDescent.CubicClosedPointSerreZeroIdealStalk
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Retractions of the actual canonical Serre stalk section -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- A linear functional taking a vector to one proves that the vector's
coordinates in any rank-two basis generate the unit ideal. -/
theorem cubicClosedPointSerreZeroIdealStalkAwayAlgebra_span_eq_top
    {R E : Type u} [CommRing R] [AddCommGroup E] [Module R E]
    (r : E →ₗ[R] R) (z : E) (hz : r z = 1) (t : E ≃ₗ[R] R × R) :
    Ideal.span ({(t z).1, (t z).2} : Set R) = ⊤ := by
  let w := t z
  let k := r.comp t.symm.toLinearMap
  have hw : w = w.1 • (1, 0) + w.2 • (0, 1) := by ext <;> simp
  have hmem : k w ∈ Ideal.span ({w.1, w.2} : Set R) := by
    rw [hw, map_add, map_smul, map_smul]
    apply Ideal.add_mem
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  have hk : k w = 1 := by
    change r (t.symm (t z)) = 1
    rw [t.symm_apply_apply]
    exact hz
  apply (Ideal.eq_top_iff_one _).mpr
  exact hk ▸ hmem

/-- An actual unit quotient stalk splits the actual original extension
stalk sequence. The resulting retraction is a left inverse of the literal
canonical stalk section, retaining its actual unit coordinate. -/
theorem cubicClosedPointSerreZeroIdealStalkAwayAlgebra_exists_retraction
    {X : Scheme.{u}} {M : X.Modules}
    (e : SerreExtensionSequenceData X M) (x : X)
    (q : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) :
    letI := schemeModuleStalkModule (show X.Modules from e.E) x
    ∃ r : ((show X.Modules from e.E).presheaf.stalk x) →ₗ[X.presheaf.stalk x]
        X.presheaf.stalk x,
      r.comp (serreExtensionStalkCanonicalSection e x) = LinearMap.id := by
  let F := schemeModuleStalkModuleFunctor X x
  letI : F.Additive := by dsimp [F]; infer_instance
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  letI : PreservesFiniteLimits F := by dsimp [F]; infer_instance
  letI : PreservesFiniteColimits F := by dsimp [F]; infer_instance
  letI := schemeModuleStalkModule (show X.Modules from e.E) x
  letI : CategoryTheory.Projective (e.complex.map F).X₃ := by
    change CategoryTheory.Projective (F.obj M)
    exact CategoryTheory.Projective.of_iso q.symm inferInstance
  let s := (e.shortExact.map_of_exact F).splittingOfProjective
  let a := schemeModuleUnitStalkIso X x
  let r := (s.r ≫ a.hom).hom
  refine ⟨r, ?_⟩
  have h : (a.inv ≫ (e.complex.map F).f) ≫ (s.r ≫ a.hom) = 𝟙 _ := by
    simp only [Category.assoc, s.f_r_assoc, a.inv_hom_id]
  have hi : ModuleCat.ofHom (serreExtensionStalkCanonicalSection e x) =
      a.inv ≫ (e.complex.map F).f := by rfl
  rw [← hi] at h
  exact ModuleCat.hom_ext_iff.mp h

end PfaffianDescent
